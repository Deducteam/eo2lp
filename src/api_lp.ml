(* api_lp.ml
   LambdaPi interface layer *)

let verbose = ref false
let set_verbose v = verbose := v

(* Debug context: tracks what symbol/module is currently being encoded *)
let current_module = ref ""
let current_symbol = ref ""
let current_phase = ref ""   (* e.g., "elaborate", "encode", "resolve" *)
let set_current_module m = current_module := m
let set_current_symbol s = current_symbol := s
let set_current_phase p = current_phase := p
let get_current_context () =
  let parts = [!current_module; !current_symbol; !current_phase]
    |> List.filter (fun s -> s <> "")
  in
  String.concat ":" parts

(* Error formatting with context *)
let format_error msg =
  let ctx = get_current_context () in
  if ctx = "" then msg
  else Printf.sprintf "[%s] %s" ctx msg

let fail msg = failwith (format_error msg)
let failf fmt = Printf.ksprintf fail fmt

(* LambdaPi modules *)
module Term      = Core.Term
module Sign      = Core.Sign
module Sig_state = Core.Sig_state
module Print     = Core.Print
module Ctxt      = Core.Ctxt
module LibTerm   = Core.LibTerm
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
let mk_Type   = Term.mk_Type
let mk_Appl   = Term.mk_Appl
let mk_Prod   = Term.mk_Prod
let mk_Abst   = Term.mk_Abst
let mk_Plac   = Term.mk_Plac
let mk_Patt   = Term.mk_Patt
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
let resolve_term ?(debug=false) ?(ctx=[]) ?expected_ty t =
  if not (has_plac t) then t
  else
    try
      let prob = Term.new_problem () in
      (* Use check if expected type provided, otherwise infer *)
      let result = match expected_ty with
        | Some exp_ty ->
          Core.Infer.check_noexn prob ctx t exp_ty
          |> Option.map (fun resolved -> (resolved, exp_ty))
        | None ->
          Core.Infer.infer_noexn prob ctx t
      in
      match result with
      | Some (resolved, ty) ->
        let _ = Core.Unif.solve_noexn prob in
        let cleaned = try Term.cleanup resolved with _ -> resolved in
        (* Only print debug output if there are still unsolved metas in the result *)
        if debug && has_unsolved_metas cleaned then begin
          Timed.(Print.print_implicits := true);
          Timed.(Print.do_not_qualify := true);
          Format.eprintf "  @[<v 2>\027[33m[%s]\027[0m resolve failed:@," (get_current_context ());
          Format.eprintf "term: %a@," Print.term t;
          Format.eprintf "got:  %a@," Print.term cleaned;
          Format.eprintf "type: %a@]@.@." Print.term ty
        end;
        cleaned
      | None ->
        if debug then begin
          Timed.(Print.print_implicits := true);
          Timed.(Print.do_not_qualify := true);
          Format.eprintf "  @[<v 2>\027[33m[%s]\027[0m infer failed:@," (get_current_context ());
          Format.eprintf "term: %a@]@.@." Print.term t
        end;
        t
    with e ->
      if debug then begin
        Format.eprintf "  @[<v 2>\027[33m[%s]\027[0m exception:@," (get_current_context ());
        Format.eprintf "%s@]@.@." (Printexc.to_string e)
      end;
      t

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

(* τ {|eo::Type|} term, set when prelude is loaded *)
let tau_eo_type_ref : term option ref = ref None

(* Bind unsolved metas as implicit parameters *)
let bind_unsolved_metas t =
  let metas = collect_unsolved_metas t in
  if metas = [] then (t, [])
  else
    (* All type-level metas should have type τ {|eo::Type|} *)
    let tau_eo_type = match !tau_eo_type_ref with
      | Some t -> t
      | None -> mk_Kind  (* fallback *)
    in
    let meta_to_var =
      List.map (fun (m, _ty) ->
        let name = "v" ^ string_of_int m.Term.meta_key in
        (m, new_var name, tau_eo_type))
        metas
    in
    let rec subst term = match term with
      | Term.Meta (m, _) ->
        (match List.find_opt
                 (fun (m', _, _) -> m == m')
                 meta_to_var
         with
         | Some (_, v, _) -> mk_Vari v
         | None -> term)
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

(* Check if a type is a Proof type *)
let is_proof_type ty =
  match ty with
  | Term.Appl (Term.Symb s, _) -> s.Term.sym_name = "Proof"
  | _ -> false

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

let is_excluded_stdlib_path path =
  List.length path >= 2 &&
  List.hd path = "Stdlib" &&
  List.nth path 1 = "Nat"

let find_symbol_global name =
  let result = ref None in
  Path.Map.iter
    (fun path sign ->
       if !result = None && not (is_excluded_stdlib_path path) then
         result := find_in sign name)
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
    failf "unresolved placeholders in type of '%s'" name;
  let ty_final, extra_impl =
    if has_unsolved_metas ty_resolved then
      let ty', new_params = bind_unsolved_metas ty_resolved in
      if List.length new_params > 3 then
        failf "too many unsolved metas (%d) in '%s'" (List.length new_params) name
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
let set_print_implicits b = Timed.(Print.print_implicits := b)
let set_print_domains   b = Timed.(Print.print_domains := b)
let set_do_not_qualify  b = Timed.(Print.do_not_qualify := b)

(* Check if term is τ {|eo::Type|} which should print as Set *)
let is_tau_eo_type = function
  | Term.Appl (Term.Symb tau_sym, Term.Symb eo_type_sym) ->
    tau_sym.Term.sym_name = "τ" &&
    eo_type_sym.Term.sym_name = "{|eo::Type|}"
  | _ -> false

(* Custom term printer that simplifies τ {|eo::Type|} to Set *)
let print_term ppf t =
  if is_tau_eo_type t then
    Format.fprintf ppf "Set"
  else
    Print.term ppf t

(* Prelude *)
let prelude : sign option ref = ref None

let prelude_sig () =
  match !prelude with
  | Some s -> s
  | None   -> failwith "Prelude not initialized"

let init prelude_sign =
  prelude := Some prelude_sign;
  (* Set τ {|eo::Type|} for binding unsolved metas *)
  (match find_symbol_global "τ", find_in prelude_sign "{|eo::Type|}" with
   | Some tau_sym, Some eo_type ->
     tau_eo_type_ref := Some (mk_Appl (mk_Symb tau_sym, mk_Symb eo_type))
   | _ -> ())

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
let dep_arrow_sym () = find "⤳d"
let app_sym ()     = find "APP"
let eo_type_sym () = find "{|eo::Type|}"
let eo_as_sym ()   = find "{|eo::as|}"

(* Name encoding *)
let lp_keywords = [
  "as"; "in"; "let"; "open"; "require"; "rule";
  "symbol"; "with"; "type"; "TYPE"; "Set"; "repeat"
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

let find_sym name =
  (* Try both unescaped and escaped versions of the name *)
  let names = [name; esc name] |> List.sort_uniq String.compare in
  let try_find n =
    match find_symbol n with
    | Some s -> Some s
    | None ->
      match find_in_deps n with
      | Some s -> Some s
      | None ->
        match find_in (prelude_sig ()) n with
        | Some s -> Some s
        | None -> find_symbol_global n
  in
  List.find_map try_find names

let get_sym name =
  match find_sym name with
  | Some s -> s
  | None ->
    failf "Symbol `%s` not found" name

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

(* Unwrap τ from a term: τ T -> T *)
let un_tau = function
  | Term.Appl (Term.Symb s, t) when s.Term.sym_name = "τ" -> t
  | t -> t  (* If not τ-wrapped, return as-is *)

let hol_arrow t1 t2 =
  add_args (mk_Symb (arrow_sym ())) [t1; t2]

(* Dependent arrow: T ⤳d F where F : τ T → Set
   τ (T ⤳d F) ↪ Π x : τ T, τ (F x) *)
let hol_dep_arrow t1 f =
  add_args (mk_Symb (dep_arrow_sym ())) [t1; f]

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
     (* Definition with inferred type - extract params from lambda *)
     (match sym_def with
      | Some def ->
        let params, body = extract_lambda_params def sym_impl in
        if params <> [] then begin
          List.iter (print_param ppf) params;
          set_print_implicits false;
          Format.fprintf ppf " ≔ %a" print_term body
        end else begin
          set_print_implicits false;
          Format.fprintf ppf " ≔ %a" print_term def
        end
      | None -> ())
   | _ ->
     (* Has explicit type - extract params from Π-binders *)
     let params, ret_ty = extract_params sym_ty sym_impl in
     let n = List.length params in
     if params <> [] then
       List.iter (print_param ppf) params;
     (* Print return type if not Kind *)
     (match ret_ty with
      | Term.Kind -> ()
      | _ -> Format.fprintf ppf " : %a" print_term ret_ty);
     (* Print definition if present *)
     (match sym_def with
      | Some def ->
        (* Keep print_implicits ON for proof steps (type is Proof ...) *)
        if not (is_proof_type ret_ty) then
          set_print_implicits false;
        Format.fprintf ppf " ≔ %a" print_term (unwrap_lambdas n def)
      | None -> ()));
  set_print_implicits false;
  set_print_domains false;
  set_do_not_qualify false;
  Format.fprintf ppf ";@."

(* Print a single rule clause (LHS ↪ RHS) without keyword *)
let print_rule_clause ppf (sym, rule) =
  set_print_implicits true;
  set_do_not_qualify true;
  (* Check if this is a coercion rule (head symbol is "coerce") *)
  let is_coerce = sym.Term.sym_name = "coerce" in
  if is_coerce then
    Format.fprintf ppf "coerce"
  else
    (* Use @ prefix to force implicits on head symbol *)
    Format.fprintf ppf "@%s" sym.Term.sym_name;
  (* Wrap each LHS arg in parentheses *)
  List.iter
    (fun arg -> Format.fprintf ppf " (%a)" print_term arg)
    rule.Term.lhs;
  Format.fprintf ppf " ↪ %a" print_term rule.Term.rhs;
  set_print_implicits false;
  set_do_not_qualify false

(* Print a group of rules for the same symbol, joined with "with" *)
let print_rules ppf rules =
  match rules with
  | [] -> ()
  | [(sym, _) as first] ->
    (* Single rule: use coerce_rule for coercion, rule otherwise *)
    let is_coerce = sym.Term.sym_name = "coerce" in
    if is_coerce then
      Format.fprintf ppf "coerce_rule %a;@." print_rule_clause first
    else
      Format.fprintf ppf "rule %a;@." print_rule_clause first
  | (sym, _) :: _ ->
    (* Check if coerce - coerce_rule doesn't support "with" *)
    let is_coerce = sym.Term.sym_name = "coerce" in
    if is_coerce then
      (* Print each coerce rule separately *)
      List.iter (fun r ->
        Format.fprintf ppf "coerce_rule %a;@." print_rule_clause r)
        rules
    else begin
      (* Multiple rules: join with "with" *)
      let first = List.hd rules in
      let rest = List.tl rules in
      Format.fprintf ppf "rule %a@." print_rule_clause first;
      List.iteri (fun i r ->
        let is_last = (i = List.length rest - 1) in
        if is_last then
          Format.fprintf ppf "with %a;@." print_rule_clause r
        else
          Format.fprintf ppf "with %a@." print_rule_clause r)
        rest
    end

let print_signature ppf ~prelude_module ~deps _sign rules ~after_rules_map =
  let open_deps =
    if deps = [] then [prelude_module] else deps
  in
  Format.fprintf ppf "require open %s;@.@."
    (String.concat " " open_deps);
  (* Track which rules have been printed *)
  let printed_rules = Hashtbl.create (List.length rules) in
  (* Print each symbol followed by its rules (grouped with "with") *)
  let local_syms = get_symbol_order () in
  List.iter (fun sym ->
    print_symbol ppf sym;
    (* Collect all rules for this symbol *)
    let sym_rules = List.filter_map (fun (i, (rule_sym, rule)) ->
      if rule_sym == sym then begin
        Hashtbl.add printed_rules i ();
        Some (rule_sym, rule)
      end else None)
      (List.mapi (fun i r -> (i, r)) rules)
    in
    print_rules ppf sym_rules;
    (* Print any after_rules associated with this symbol *)
    (match Hashtbl.find_opt after_rules_map sym with
     | Some after_rs ->
       (* Group after_rules by their head symbol *)
       let grouped = Hashtbl.create 4 in
       List.iter (fun ((rule_sym, _) as r) ->
         let key = rule_sym.Term.sym_name in
         let existing = try Hashtbl.find grouped key with Not_found -> [] in
         Hashtbl.replace grouped key (r :: existing))
         after_rs;
       Hashtbl.iter (fun _ rs -> print_rules ppf (List.rev rs)) grouped
     | None -> ()))
  local_syms;
  (* Print any remaining rules (for external symbols like ⪽) *)
  let remaining = List.filter_map (fun (i, r) ->
    if Hashtbl.mem printed_rules i then None else Some r)
    (List.mapi (fun i r -> (i, r)) rules)
  in
  (* Group remaining rules by symbol *)
  let grouped = Hashtbl.create 16 in
  List.iter (fun ((sym, _) as r) ->
    let key = sym.Term.sym_name in
    let existing = try Hashtbl.find grouped key with Not_found -> [] in
    Hashtbl.replace grouped key (r :: existing))
    remaining;
  Hashtbl.iter (fun _ rs -> print_rules ppf (List.rev rs)) grouped

(* File operations *)
let rec mkdir_p dir =
  if not (Sys.file_exists dir) then begin
    mkdir_p (Filename.dirname dir);
    Sys.mkdir dir 0o755
  end

let write_lp_file filepath ~prelude_module ~deps sign rules ~after_rules_map =
  let dir = Filename.dirname filepath in
  if dir <> "." && dir <> "" then mkdir_p dir;
  let oc  = open_out filepath in
  let ppf = Format.formatter_of_out_channel oc in
  print_signature ppf ~prelude_module ~deps sign rules ~after_rules_map;
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

let check_file ?verbose:_ output_dir rel_path =
  let cmd =
    Printf.sprintf
      "cd %s && NO_COLOR=1 timeout 1 lambdapi check -c -w %s 2>&1"
      output_dir rel_path
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
    (* Remove ANSI escape codes *)
    |> Str.global_replace (Str.regexp "\027\\[[0-9;]*m") ""
    (* Remove "Start checking ..." line *)
    |> Str.global_replace (Str.regexp "Start checking [^\n]*\n?") ""
    (* Simplify absolute paths - keep just filename:line:col *)
    |> Str.global_replace (Str.regexp "\\[/[^]]*/" ) "["
    |> String.trim
  in
  match status with
  | Unix.WEXITED 0   -> Check_ok
  | Unix.WEXITED 124 -> Check_error "timeout"
  | _                -> Check_error output

let is_check_ok = function
  | Check_ok -> true
  | _        -> false
