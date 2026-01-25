(* api_lp.ml
   LambdaPi interface layer *)

let verbose = ref false
let set_verbose v = verbose := v

(* LambdaPi modules *)
module Term      = Core.Term
module Sign      = Core.Sign
module Sig_state = Core.Sig_state
module Print     = Core.Print
module Ctxt      = Core.Ctxt
module Compile   = Handle.Compile
module Package   = Parsing.Package
module Library   = Common.Library
module Path      = Common.Path
module Pos       = Common.Pos

(* Types *)
type term = Term.term
type sym  = Term.sym
type var  = Term.var
type rule = Term.rule
type sign = Sign.t
type ctxt = Term.ctxt

(* Term constructors *)
let mk_Symb   = Term.mk_Symb
let mk_Vari   = Term.mk_Vari
let mk_Kind   = Term.mk_Kind
let mk_Appl   = Term.mk_Appl
let mk_Prod   = Term.mk_Prod
let mk_Abst   = Term.mk_Abst
let mk_Plac   = Term.mk_Plac
let add_args  = Term.add_args
let new_var   = Term.new_var
let bind_var  = Term.bind_var
let unbind    = Term.unbind
let base_name = Term.base_name

(* Contexts *)
let empty_ctxt : ctxt = []

let ctxt_add ctx v ty =
  (v, ty, None) :: ctx

let ctxt_to_prod = Ctxt.to_prod

let ctxt_to_abst ctx t =
  List.fold_left
    (fun acc (v, ty, _) -> mk_Abst (ty, bind_var v acc))
    t ctx

let ctxt_find ctx name =
  List.find_map
    (fun (v, _, _) ->
       if base_name v = name then Some v else None)
    ctx

(* Term predicates *)
let rec has_unsolved_metas = function
  | Term.Meta (m, _) ->
    Option.is_none Timed.(!(m.Term.meta_value))
  | Term.Appl (t1, t2) ->
    has_unsolved_metas t1 || has_unsolved_metas t2
  | Term.Abst (a, b) | Term.Prod (a, b) ->
    has_unsolved_metas a ||
    has_unsolved_metas (snd (unbind b))
  | _ -> false

let rec has_plac = function
  | Term.Plac _ -> true
  | Term.Appl (t1, t2) ->
    has_plac t1 || has_plac t2
  | Term.Abst (a, b) | Term.Prod (a, b) ->
    has_plac a || has_plac (snd (unbind b))
  | _ -> false

(* Resolve placeholders via type inference *)
let resolve_term ?(debug=false) t =
  if not (has_plac t) then t
  else
    try
      let prob = Term.new_problem () in
      match Core.Infer.infer_noexn prob [] t with
      | Some (resolved, _) ->
        let _ = Core.Unif.solve_noexn prob in
        (try Term.cleanup resolved with _ -> resolved)
      | None -> t
    with _ -> t

(* Collect unsolved metas *)
let collect_unsolved_metas t =
  let metas = ref [] in
  let rec go = function
    | Term.Meta (m, _)
      when Option.is_none Timed.(!(m.Term.meta_value)) ->
      if not (List.exists (fun (m', _) -> m == m') !metas)
      then metas := (m, Timed.(!(m.Term.meta_type))) :: !metas
    | Term.Appl (t1, t2) -> go t1; go t2
    | Term.Abst (a, b) | Term.Prod (a, b) ->
      go a; go (snd (unbind b))
    | _ -> ()
  in
  go t; !metas

(* Convert unsolved metas to wildcards *)
let rec metas_to_wildcards = function
  | Term.Meta (m, _)
    when Option.is_none Timed.(!(m.Term.meta_value)) ->
    mk_Plac false
  | Term.Appl (t1, t2) ->
    mk_Appl (metas_to_wildcards t1, metas_to_wildcards t2)
  | Term.Abst (a, b) ->
    let x, body = unbind b in
    mk_Abst (metas_to_wildcards a,
             bind_var x (metas_to_wildcards body))
  | Term.Prod (a, b) ->
    let x, body = unbind b in
    mk_Prod (metas_to_wildcards a,
             bind_var x (metas_to_wildcards body))
  | t -> t

(* Bind unsolved metas as implicit parameters *)
let bind_unsolved_metas t =
  let metas = collect_unsolved_metas t in
  if metas = [] then (t, [])
  else
    let meta_to_var =
      List.map (fun (m, ty) ->
        let name = "v" ^ string_of_int m.Term.meta_key in
        (m, new_var name, ty))
        metas
    in
    let rec subst = function
      | Term.Meta (m, _) ->
        (match List.find_opt
                 (fun (m', _, _) -> m == m')
                 meta_to_var
         with
         | Some (_, v, _) -> mk_Vari v
         | None -> t)
      | Term.Appl (t1, t2) ->
        mk_Appl (subst t1, subst t2)
      | Term.Abst (a, b) ->
        let x, body = unbind b in
        mk_Abst (subst a, bind_var x (subst body))
      | Term.Prod (a, b) ->
        let x, body = unbind b in
        mk_Prod (subst a, bind_var x (subst body))
      | t -> t
    in
    (subst t, List.map (fun (_, v, ty) -> (v, ty)) meta_to_var)

(* Signature state *)
let current_sign : sign option ref = ref None
let symbol_order : sym list ref    = ref []
let current_deps  : Path.t list ref = ref []

let get_sign () =
  match !current_sign with
  | Some s -> s
  | None   -> failwith "LambdaPi signature not initialized"

let get_symbol_order () =
  List.rev !symbol_order

let init_sign ?(deps = []) path =
  current_deps := deps;
  match Path.Map.find_opt path Timed.(!(Sign.loaded)) with
  | Some sign ->
    current_sign := Some sign;
    symbol_order := [];
    sign
  | None ->
    let sign = Sig_state.create_sign path in
    Timed.(Sign.loaded :=
             Path.Map.add path sign !(Sign.loaded));
    current_sign := Some sign;
    symbol_order := [];
    sign

let reset_sign () =
  current_sign := None;
  symbol_order := [];
  current_deps := []

(* Symbol storage for printing *)
let symbol_types : (string, term) Hashtbl.t =
  Hashtbl.create 32
let symbol_defs : (string, term) Hashtbl.t =
  Hashtbl.create 32

let reset_symbol_storage () =
  Hashtbl.clear symbol_types;
  Hashtbl.clear symbol_defs

(* Check for Stdlib.Nat symbols *)
let rec contains_nat_symbol = function
  | Term.Symb s ->
    let p = s.Term.sym_path in
    List.length p >= 2 &&
    List.nth p 0 = "Stdlib" &&
    List.nth p 1 = "Nat"
  | Term.Appl (t1, t2) ->
    contains_nat_symbol t1 || contains_nat_symbol t2
  | Term.Abst (a, b) | Term.Prod (a, b) ->
    contains_nat_symbol a ||
    contains_nat_symbol (snd (unbind b))
  | _ -> false

(* Symbol lookup *)
let find_in sign name =
  try Some (Sign.find sign name)
  with Not_found -> None

let find_symbol name =
  find_in (get_sign ()) name

let find_symbol_global name =
  let result = ref None in
  Path.Map.iter
    (fun _ sign ->
       if !result = None then result := find_in sign name)
    Timed.(!(Sign.loaded));
  !result

(* Add symbol to signature *)
let add_symbol_to_sign
    ?(expo=Term.Public)
    ?(prop=Term.Const)
    ?(mstrat=Term.Eager)
    ?(impl=[])
    name ty
  =
  let sign = get_sign () in
  let ty_resolved = resolve_term ty in
  if has_plac ty_resolved then
    failwith (Printf.sprintf
      "Cannot add symbol '%s': unresolved placeholders"
      name);
  let ty_final, extra_impl =
    if has_unsolved_metas ty_resolved then
      let ty', new_params = bind_unsolved_metas ty_resolved in
      if List.length new_params > 3 then
        failwith (Printf.sprintf
          "Symbol '%s' has too many unsolved metas"
          name)
      else
        let ty_wrapped =
          List.fold_right
            (fun (v, pty) acc -> mk_Prod (pty, bind_var v acc))
            new_params ty'
        in
        (ty_wrapped, List.map (fun _ -> true) new_params)
    else
      (ty_resolved, [])
  in
  let sym =
    Sign.add_symbol sign expo prop mstrat false
      (Pos.none name) None ty_final (extra_impl @ impl)
  in
  Hashtbl.replace symbol_types name ty_final;
  symbol_order := sym :: !symbol_order;
  sym

let add_constant ?(impl=[]) name ty =
  add_symbol_to_sign ~prop:Term.Const ~impl name ty

let add_sequential ?(impl=[]) name ty =
  add_symbol_to_sign
    ~prop:Term.Defin ~mstrat:Term.Sequen ~impl name ty

let add_definition ?(impl=[]) name ty def =
  let sign = get_sign () in
  let ty_resolved =
    match ty with
    | Some t -> resolve_term t
    | None   -> mk_Kind
  in
  let def_resolved = resolve_term def in
  let def_for_print =
    if contains_nat_symbol def_resolved then
      if has_plac def then def
      else metas_to_wildcards def_resolved
    else if has_unsolved_metas def_resolved then
      metas_to_wildcards def_resolved
    else
      def_resolved
  in
  let sym =
    Sign.add_symbol sign
      Term.Public Term.Defin Term.Eager false
      (Pos.none name) None ty_resolved impl
  in
  Timed.(sym.Term.sym_def := Some def_resolved);
  Hashtbl.replace symbol_types name ty_resolved;
  Hashtbl.replace symbol_defs name def_for_print;
  symbol_order := sym :: !symbol_order;
  sym

(* Compilation *)
let compile ?(force=false) path =
  let run () = Compile.compile ~force path in
  if !verbose then run ()
  else begin
    flush_all ();
    let old_out = Unix.dup Unix.stdout in
    let old_err = Unix.dup Unix.stderr in
    let null = Unix.openfile "/dev/null" [Unix.O_WRONLY] 0 in
    Unix.dup2 null Unix.stdout;
    Unix.dup2 null Unix.stderr;
    Unix.close null;
    match run () with
    | result ->
      Unix.dup2 old_out Unix.stdout;
      Unix.dup2 old_err Unix.stderr;
      Unix.close old_out;
      Unix.close old_err;
      result
    | exception e ->
      Unix.dup2 old_out Unix.stdout;
      Unix.dup2 old_err Unix.stderr;
      Unix.close old_out;
      Unix.close old_err;
      raise e
  end

let init_library () =
  Library.set_lib_root None

let apply_package_config =
  Package.apply_config

(* Printing helpers *)
let print_term         = Print.term
let set_print_implicits b = Timed.(Print.print_implicits := b)
let set_print_domains   b = Timed.(Print.print_domains := b)
let set_do_not_qualify  b = Timed.(Print.do_not_qualify := b)

(* Prelude *)
let prelude : sign option ref = ref None

let prelude_sig () =
  match !prelude with
  | Some s -> s
  | None   -> failwith "Prelude not initialized"

let init prelude_sign =
  prelude := Some prelude_sign

let reset () =
  prelude := None;
  reset_symbol_storage ()

let find name =
  match find_in (prelude_sig ()) name with
  | Some s -> s
  | None ->
    match find_symbol_global name with
    | Some s -> s
    | None ->
      failwith (Printf.sprintf "Symbol '%s' not found." name)

(* Prelude symbols *)
let tau ()         = find "τ"
let arrow_sym ()   = find "⤳"
let app_sym ()     = find "APP"
let eo_type_sym () = find "{|eo::Type|}"
let eo_as_sym ()   = find "{|eo::as|}"

(* Name encoding *)
let lp_keywords = [
  "as"; "in"; "let"; "open"; "require"; "rule";
  "symbol"; "with"; "type"; "TYPE"; "Set"
]

let invalid_chars = [
  '\t'; '\r'; '\n'; ' '; ':'; ','; ';'; '`';
  '('; ')'; '{'; '}'; '['; ']'; '"'; '.';
  '@'; '$'; '|'; '?'; '/'
]

let esc s =
  if String.exists (fun c -> List.mem c invalid_chars) s
     || List.mem s lp_keywords
     || Option.is_some (int_of_string_opt s)
  then "{|" ^ s ^ "|}"
  else s

(* Symbol lookup with dependencies *)
let find_in_deps name =
  List.find_map
    (fun dep_path ->
       Option.bind
         (Path.Map.find_opt dep_path Timed.(!(Sign.loaded)))
         (fun sign -> find_in sign name))
    !current_deps

let is_excluded_stdlib_symbol s =
  let p = s.Term.sym_path in
  List.length p >= 2 &&
  List.hd p = "Stdlib" &&
  List.nth p 1 = "Nat"

let find_sym name =
  match find_symbol name with
  | Some s -> Some s
  | None ->
    match find_in_deps name with
    | Some s -> Some s
    | None ->
      match find_in (prelude_sig ()) name with
      | Some s -> Some s
      | None ->
        match find_symbol_global name with
        | Some s when not (is_excluded_stdlib_symbol s) ->
          Some s
        | _ -> None

let get_sym name =
  match find_sym name with
  | Some s -> s
  | None ->
    failwith (Printf.sprintf "Symbol not found: %s" name)

(* Symbol application with implicits *)
let rec count_leading_impl = function
  | true :: rest -> 1 + count_leading_impl rest
  | _ -> 0

let enc_sym s =
  let n = count_leading_impl s.Term.sym_impl in
  add_args (mk_Symb s) (List.init n (fun _ -> mk_Plac false))

(* Term builders *)
let tau_of t =
  mk_Appl (mk_Symb (tau ()), t)

let hol_arrow t1 t2 =
  add_args (mk_Symb (arrow_sym ())) [t1; t2]

let hol_app t1 t2 =
  add_args (enc_sym (app_sym ())) [t1; t2]

let eo_type () =
  mk_Symb (eo_type_sym ())

let eo_as t1 t2 =
  add_args (enc_sym (eo_as_sym ())) [t2; t1]

(* Integer encoding *)
let z0 ()    = find "Z0"
let zpos ()  = find "Zpos"
let zneg ()  = find "Zneg"
let pos_h () = find "H"
let pos_i () = find "I"
let pos_o () = find "O"

let rec enc_positive n =
  assert (n > 0);
  if n = 1 then mk_Symb (pos_h ())
  else
    let sym = if n mod 2 = 0 then pos_o () else pos_i () in
    mk_Appl (mk_Symb sym, enc_positive (n / 2))

let enc_int n =
  if n = 0 then mk_Symb (z0 ())
  else if n > 0 then mk_Appl (mk_Symb (zpos ()), enc_positive n)
  else mk_Appl (mk_Symb (zneg ()), enc_positive (-n))

let ghost_sym name =
  let ghost_path = Sign.Ghost.path in
  match find_symbol_global name with
  | Some s when s.Term.sym_path = ghost_path -> s
  | _ ->
    let sym =
      Term.create_sym ghost_path
        Term.Public Term.Const Term.Eager false
        (Pos.none name) None mk_Kind []
    in
    Timed.(Sign.Ghost.sign.Sign.sign_symbols :=
      Lplib.Extra.StrMap.add name sym
        !(Sign.Ghost.sign.Sign.sign_symbols));
    sym

(* Printing support *)
let rec unwrap_lambdas n t =
  if n <= 0 then t
  else match t with
    | Term.Abst (_, b) -> unwrap_lambdas (n-1) (snd (unbind b))
    | _ -> t

let rec extract_params ty impl =
  match ty with
  | Term.Prod (a, b) ->
    let x, body = unbind b in
    let is_impl, rest =
      match impl with
      | i :: r -> (i, r)
      | []     -> (false, [])
    in
    let rest_params, ret = extract_params body rest in
    ((base_name x, a, is_impl) :: rest_params, ret)
  | _ -> ([], ty)

let rec extract_lambda_params tm impl =
  match tm with
  | Term.Abst (a, b) ->
    let x, body = unbind b in
    let is_impl, rest =
      match impl with
      | i :: r -> (i, r)
      | []     -> (false, [])
    in
    let rest_params, ret = extract_lambda_params body rest in
    ((base_name x, a, is_impl) :: rest_params, ret)
  | _ -> ([], tm)

let print_param ppf (name, ty, is_impl) =
  if is_impl then
    Format.fprintf ppf " [%s : %a]" name print_term ty
  else
    Format.fprintf ppf " (%s : %a)" name print_term ty

let print_symbol ppf sym =
  let name = sym.Term.sym_name in
  set_do_not_qualify true;
  set_print_domains true;
  Print.expo ppf sym.Term.sym_expo;
  Print.prop ppf sym.Term.sym_prop;
  Print.match_strat ppf sym.Term.sym_mstrat;
  Format.fprintf ppf "symbol %s" name;
  let sym_ty =
    Option.value
      (Hashtbl.find_opt symbol_types name)
      ~default:mk_Kind
  in
  let sym_def  = Hashtbl.find_opt symbol_defs name in
  let sym_impl = sym.Term.sym_impl in
  set_print_implicits true;
  (match sym_ty with
   | Term.Kind ->
     (match sym_def with
      | Some def ->
        let params, body =
          extract_lambda_params def sym_impl
        in
        if params <> [] then begin
          List.iter (print_param ppf) params;
          Format.fprintf ppf " ≔ %a" print_term body
        end else
          Format.fprintf ppf " ≔ %a" print_term def
      | None -> ())
   | _ ->
     let params, _ = extract_params sym_ty sym_impl in
     let n = List.length params in
     if sym_def <> None && n > 0 then begin
       List.iter (print_param ppf) params;
       match sym_def with
       | Some def ->
         Format.fprintf ppf " ≔ %a"
           print_term (unwrap_lambdas n def)
       | None -> ()
     end else begin
       Format.fprintf ppf " : %a" print_term sym_ty;
       match sym_def with
       | Some def ->
         Format.fprintf ppf " ≔ %a" print_term def
       | None -> ()
     end);
  set_print_implicits false;
  set_print_domains false;
  set_do_not_qualify false;
  Format.fprintf ppf ";@."

let print_signature ppf ~prelude_module ~deps _sign rules =
  Format.fprintf ppf "require %s as eo;@." prelude_module;
  let open_deps =
    if deps = [] then [prelude_module] else deps
  in
  Format.fprintf ppf "require open %s;@.@."
    (String.concat " " open_deps);
  List.iter (print_symbol ppf) (get_symbol_order ());
  List.iter
    (fun (sym, rule) ->
       set_do_not_qualify true;
       set_print_implicits true;
       Format.fprintf ppf "rule %s" sym.Term.sym_name;
       List.iter
         (fun arg -> Format.fprintf ppf " %a" print_term arg)
         rule.Term.lhs;
       Format.fprintf ppf " ↪ %a;@." print_term rule.Term.rhs;
       set_print_implicits false;
       set_do_not_qualify false)
    rules

(* File operations *)
let rec mkdir_p dir =
  if not (Sys.file_exists dir) then begin
    mkdir_p (Filename.dirname dir);
    Sys.mkdir dir 0o755
  end

let write_lp_file filepath ~prelude_module ~deps sign rules =
  let dir = Filename.dirname filepath in
  if dir <> "." && dir <> "" then mkdir_p dir;
  let oc  = open_out filepath in
  let ppf = Format.formatter_of_out_channel oc in
  print_signature ppf ~prelude_module ~deps sign rules;
  Format.pp_print_flush ppf ();
  close_out oc

let generate_pkg_file output_dir pkg_name =
  let path = Filename.concat output_dir "lambdapi.pkg" in
  let oc = open_out path in
  Printf.fprintf oc "package_name = %s\n" pkg_name;
  Printf.fprintf oc "root_path = %s\n" pkg_name;
  close_out oc

let generate_prelude output_dir =
  let src = "src/Prelude.lp" in
  let dst = Filename.concat output_dir "Prelude.lp" in
  let ic  = open_in src in
  let oc  = open_out dst in
  (try
     while true do
       output_string oc (input_line ic ^ "\n")
     done
   with End_of_file -> ());
  close_in ic;
  close_out oc

(* LambdaPi checking *)
type check_result =
  | Check_ok
  | Check_error of string

let check_file ?(verbose=false) output_dir rel_path =
  let debug = if verbose then "--debug=iu" else "" in
  let cmd =
    Printf.sprintf
      "cd %s && NO_COLOR=1 timeout 120 lambdapi check %s -w %s 2>&1"
      output_dir debug rel_path
  in
  let ic  = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try
     while true do Buffer.add_channel buf ic 1 done
   with End_of_file -> ());
  let status = Unix.close_process_in ic in
  let output =
    Buffer.contents buf
    |> String.trim
    |> Str.global_replace
         (Str.regexp "\027\\[[0-9;]*m") ""
  in
  match status with
  | Unix.WEXITED 0   -> Check_ok
  | Unix.WEXITED 124 -> Check_error "timeout"
  | _                -> Check_error output

let is_check_ok = function
  | Check_ok -> true
  | _        -> false
