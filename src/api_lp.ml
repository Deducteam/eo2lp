(* api_lp.ml
   LambdaPi interface layer *)

(* Log severity levels *)
type log_level = Silent | Error | Warn | Info

let log_level = ref Silent
let set_log_level l = log_level := l

(* Backward compat: verbose = Info threshold *)
let verbose = ref false
let set_verbose v =
  verbose := v;
  if v && !log_level = Silent then log_level := Info

let log_level_of_string = function
  | "info"  -> Info
  | "warn"  -> Warn
  | "error" -> Error
  | s -> failwith (Printf.sprintf "Unknown log level: %s (expected info, warn, error)" s)

let log_level_geq level =
  let to_int = function Silent -> 0 | Error -> 1 | Warn -> 2 | Info -> 3 in
  to_int !log_level >= to_int level

(* Debug context: tracks what symbol/module is currently being encoded *)
let current_module = ref ""
let current_symbol = ref ""
let current_phase = ref ""   (* e.g., "elab", "encode", "resolve" *)
let set_current_module m = current_module := m
let set_current_symbol s = current_symbol := s
let set_current_phase p = current_phase := p
let get_current_context () =
  let parts = [!current_module; !current_symbol; !current_phase]
    |> List.filter (fun s -> s <> "")
  in
  String.concat ":" parts

(* Severity-colored logging: info=cyan, warn=yellow, error=red *)
let log_info fmt =
  Printf.ksprintf (fun s ->
    if log_level_geq Info then
      Printf.eprintf "  \027[36m[%s]\027[0m %s\n%!" (get_current_context ()) s
  ) fmt

let log_warn fmt =
  Printf.ksprintf (fun s ->
    if log_level_geq Warn then
      Printf.eprintf "  \027[33m[%s]\027[0m %s\n%!" (get_current_context ()) s
  ) fmt

(* Format-based warn for LambdaPi printer terms — gated on warn level *)
let log_warn_pp callback =
  if log_level_geq Warn then begin
    Timed.(Core.Print.print_implicits := true);
    Timed.(Core.Print.do_not_qualify := true);
    callback (get_current_context ())
  end

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
  | Term.LLet (a, t, b) ->
    has_unsolved_metas a || has_unsolved_metas t ||
    has_unsolved_metas (snd (unbind b))
  | _ -> false

(* Check if a symbol is Stdlib.Z's "int" *)
let is_stdlib_int s =
  s.Term.sym_name = "int" && s.Term.sym_path = ["Stdlib"; "Z"]

(* Check if term contains Stdlib.Z's "int" — either as a bare symbol
   (after cleanup) or as a solved meta. This indicates incorrect resolution
   (should be Int/Real, not Stdlib.Z.int). *)
let rec has_stdlib_int = function
  | Term.Symb s -> is_stdlib_int s
  | Term.Meta (m, ts) ->
    (match Timed.(!(m.Term.meta_value)) with
     | None -> false
     | Some mb ->
       let value = Term.msubst mb ts in
       has_stdlib_int value)
  | Term.Appl (t1, t2) ->
    has_stdlib_int t1 || has_stdlib_int t2
  | Term.Abst (a, b) | Term.Prod (a, b) ->
    has_stdlib_int a ||
    has_stdlib_int (snd (unbind b))
  | _ -> false

(* Replace unsolved metas with placeholders so LambdaPi can re-infer them *)
let rec metas_to_plac = function
  | Term.Meta (m, _) when Option.is_none Timed.(!(m.Term.meta_value)) ->
    mk_Plac false
  | Term.Appl (t1, t2) ->
    Term.mk_Appl (metas_to_plac t1, metas_to_plac t2)
  | Term.Abst (a, b) ->
    let v, body = unbind b in
    Term.mk_Abst (metas_to_plac a, bind_var v (metas_to_plac body))
  | Term.Prod (a, b) ->
    let v, body = unbind b in
    Term.mk_Prod (metas_to_plac a, bind_var v (metas_to_plac body))
  | Term.LLet (a, t, b) ->
    let v, body = unbind b in
    Term.mk_LLet (metas_to_plac a, metas_to_plac t, bind_var v (metas_to_plac body))
  | t -> t

(* Replace solved metas with placeholders, UNLESS the solved value
   is a context variable (which would be needed as a pattern variable).
   Unsolved metas are always converted to placeholders. *)
let nonvar_metas_to_plac t =
  let rec go = function
    | Term.Symb s when is_stdlib_int s -> mk_Plac false
    | Term.Meta (m, ts) ->
      (match Timed.(!(m.Term.meta_value)) with
       | None -> mk_Plac false  (* unsolved *)
       | Some mb ->
         (* Substitute meta's bound vars with ts to get actual value *)
         let value = Term.msubst mb ts in
         (match value with
          | Term.Vari _ -> value  (* keep context variables *)
          | Term.Symb _ -> mk_Plac false  (* wildcard concrete symbols *)
          | Term.Meta _ -> mk_Plac false
          | _ -> go value))
    | Term.Appl (t1, t2) -> Term.mk_Appl (go t1, go t2)
    | Term.Abst (a, b) ->
      let v, body = unbind b in
      Term.mk_Abst (go a, bind_var v (go body))
    | Term.Prod (a, b) ->
      let v, body = unbind b in
      Term.mk_Prod (go a, bind_var v (go body))
    | t -> t
  in go t

(* Replace unsolved metas with a given term (for best-effort type variable filling).
   Only touches unsolved metas; solved metas and other terms are left as-is.
   Returns the modified term. *)
let rec solve_set_metas_to t replacement =
  let go t = solve_set_metas_to t replacement in
  match t with
  | Term.Meta (m, _) when Option.is_none Timed.(!(m.Term.meta_value)) ->
    replacement
  | Term.Appl (t1, t2) -> Term.mk_Appl (go t1, go t2)
  | _ -> t



let rec has_plac = function
  | Term.Plac _ -> true
  | Term.Appl (t1, t2) ->
    has_plac t1 || has_plac t2
  | Term.Abst (a, b) | Term.Prod (a, b) ->
    has_plac a || has_plac (snd (unbind b))
  | Term.LLet (a, t, b) ->
    has_plac a || has_plac t || has_plac (snd (unbind b))
  | _ -> false

(* Pretty-print a context as "x : T, y : U, ..." *)
let pp_ctx_compact () fmt ctx =
  let pp_entry fmt (v, ty, _) =
    Format.fprintf fmt "%s : %a" (Term.base_name v) Print.term ty
  in
  Format.pp_print_list
    ~pp_sep:(fun fmt () -> Format.fprintf fmt ", ")
    pp_entry fmt ctx

(* Resolve placeholders via type inference *)
let resolve_term ?(debug=false) ?(ctx=[]) ?expected_ty t =
  if not (has_plac t) then t
  else
    let saved_phase = !current_phase in
    current_phase := "resolve";
    let restore () = current_phase := saved_phase in
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
        if has_unsolved_metas cleaned && debug then
          log_warn_pp (fun lbl ->
            Format.eprintf "  \027[33m[%s]\027[0m unsolved metas:@." lbl;
            Format.eprintf "    ctx:  %a@." (pp_ctx_compact ()) ctx;
            Format.eprintf "    term: %a@." Print.term t;
            Format.eprintf "    got:  %a@." Print.term cleaned;
            Format.eprintf "    type: %a@.@." Print.term ty);
        restore (); cleaned
      | None ->
        log_warn_pp (fun lbl ->
          Format.eprintf "  \027[33m[%s]\027[0m resolve failed:@." lbl;
          Format.eprintf "    ctx:  %a@." (pp_ctx_compact ()) ctx;
          Format.eprintf "    term: %a@.@." Print.term t);
        restore (); t
    with e ->
      log_warn_pp (fun lbl ->
        Format.eprintf "  \027[33m[%s]\027[0m resolve exception:@." lbl;
        Format.eprintf "    ctx:  %a@." (pp_ctx_compact ()) ctx;
        Format.eprintf "    %s@.@." (Printexc.to_string e));
      restore (); t


(* Signature state *)
let current_sign : sign option ref = ref None
let current_deps  : Path.t list ref = ref []

let get_sign () =
  match !current_sign with
  | Some s -> s
  | None   -> failwith "LambdaPi signature not initialized"

let init_sign ?(deps = []) path =
  current_deps := deps;
  match Path.Map.find_opt path Timed.(!(Sign.loaded)) with
  | Some sign ->
    current_sign := Some sign;
    sign
  | None ->
    let sign = Sig_state.create_sign path in
    Timed.(Sign.loaded :=
             Path.Map.add path sign !(Sign.loaded));
    current_sign := Some sign;
    sign

let reset_sign () =
  current_sign := None;
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

let is_stdlib_path path =
  List.length path >= 1 && List.hd path = "Stdlib"

let find_symbol_global name =
  let result = ref None in
  let is_stdlib_result = ref true in
  Path.Map.iter
    (fun path sign ->
       if not (is_excluded_stdlib_path path) then
         match find_in sign name with
         | Some s ->
           let is_std = is_stdlib_path path in
           (* Prefer non-Stdlib symbols over Stdlib ones *)
           if !result = None || (!is_stdlib_result && not is_std) then begin
             result := Some s;
             is_stdlib_result := is_std
           end
         | None -> ())
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
  let sym =
    Sign.add_symbol sign expo prop mstrat false
      (Pos.none name) None ty impl
  in
  Hashtbl.replace symbol_types name ty;
  sym

let add_constant ?(impl=[]) name ty =
  add_symbol_to_sign ~prop:Term.Const ~impl name ty

let add_sequential ?(impl=[]) name ty =
  add_symbol_to_sign
    ~prop:Term.Defin ~mstrat:Term.Sequen ~impl name ty


let add_definition ?(impl=[]) name ty def =
  let sign = get_sign () in
  let ty_final = match ty with Some t -> t | None -> mk_Kind in
  let def_for_print =
    if contains_nat_symbol def then
      if has_plac def then def
      else metas_to_plac def
    else if has_unsolved_metas def then
      metas_to_plac def
    else
      def
  in
  let sym =
    Sign.add_symbol sign
      Term.Public Term.Defin Term.Eager false
      (Pos.none name) None ty_final impl
  in
  Timed.(sym.Term.sym_def := Some def);
  Hashtbl.replace symbol_types name ty_final;
  Hashtbl.replace symbol_defs name def_for_print;
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
    Fun.protect ~finally:(fun () ->
      Unix.dup2 old_out Unix.stdout;
      Unix.dup2 old_err Unix.stderr;
      Unix.close old_out;
      Unix.close old_err)
      run
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

(* Table mapping symbol names to their alias targets (LambdaPi terms).
   Populated by encode.ml when processing declare-consts. *)
let alias_table : (string, term) Hashtbl.t = Hashtbl.create 4

let register_alias name target = Hashtbl.replace alias_table name target

(* Reduce aliased symbols using the alias table *)
let rec reduce_aliases t =
  match t with
  | Term.Symb s ->
    (match Hashtbl.find_opt alias_table s.Term.sym_name with
     | Some target -> reduce_aliases target
     | None -> Term.mk_Symb s)
  | Term.Appl (t1, t2) -> Term.mk_Appl (reduce_aliases t1, reduce_aliases t2)
  | Term.Abst (a, b) ->
    let v, body = unbind b in
    Term.mk_Abst (reduce_aliases a, bind_var v (reduce_aliases body))
  | Term.Prod (a, b) ->
    let v, body = unbind b in
    Term.mk_Prod (reduce_aliases a, bind_var v (reduce_aliases body))
  | Term.LLet (a, t, b) ->
    let v, body = unbind b in
    Term.mk_LLet (reduce_aliases a, reduce_aliases t, bind_var v (reduce_aliases body))
  | t -> t

(* Custom term printer that simplifies τ {|eo::Type|} to Set
   and reduces literal type aliases *)
let print_term ppf t =
  let t = reduce_aliases t in
  let t = if has_unsolved_metas t then metas_to_plac t else t in
  if is_tau_eo_type t then
    Format.fprintf ppf "Set"
  else
    Print.term ppf t

(* Symbols whose printed return type text needs post-processing to add
   explicit @-prefixed implicits. Maps symbol name to a list of
   (relation_sym_name, impl_arg_text) pairs, e.g.,
   [("arith_mult_sign", [">", "T T"; "<", "T T"])] *)
let explicit_impl_replacements : (string, (string * string) list) Hashtbl.t =
  Hashtbl.create 4

(* Register that a symbol's printed return type should have specific
   relation symbols replaced with @-prefixed versions *)
let register_explicit_replacements sym_name replacements =
  Hashtbl.replace explicit_impl_replacements sym_name replacements

(* Apply @-prefix replacements to printed text.
   E.g., replace standalone ">" with "(@> T T)" *)
let apply_explicit_replacements sym_name text =
  match Hashtbl.find_opt explicit_impl_replacements sym_name with
  | None -> text
  | Some repls ->
    List.fold_left (fun acc (rel_name, impl_args) ->
      let replacement = Printf.sprintf "(@%s %s)" rel_name impl_args in
      (* Match the symbol preceded and followed by space, paren, or
         start/end of string. Use a simple string replacement for
         exact matches like " > " or " >)" *)
      let re = Str.regexp (Printf.sprintf "\\([( ]\\)%s\\([ )]\\)" (Str.quote rel_name)) in
      Str.global_replace re (Printf.sprintf "\\1%s\\2" replacement) acc
    ) text repls

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

(* Name encoding *)

(* Names that clash with LambdaPi builtins and cannot be escaped with {|...|} *)
let lp_reserved = ["Set"; "TYPE"]

(* Names that can be escaped with {|...|} to avoid clashes *)
let lp_keywords = [
  "as"; "in"; "let"; "open"; "require"; "rule";
  "symbol"; "with"; "type"; "repeat"
]

let invalid_chars = [
  '\t'; '\r'; '\n'; ' '; ':'; ','; ';'; '`';
  '('; ')'; '{'; '}'; '['; ']'; '"'; '.';
  '@'; '$'; '|'; '?'; '/'
]

let esc s =
  (* Reserved names must be prefixed to avoid clash with LambdaPi builtins *)
  if List.mem s lp_reserved then "{|eo::" ^ s ^ "|}"
  else if String.exists (fun c -> List.mem c invalid_chars) s
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

(* Find all LP symbol overloads for a base name: name, name_1, name_2, ... *)
let find_overloads base_name =
  let base = esc base_name in
  let rec go i acc =
    let n = if i = 0 then base else Printf.sprintf "%s_%d" base i in
    match find_sym n with
    | Some s -> go (i + 1) (s :: acc)
    | None -> List.rev acc
  in
  go 0 []


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
     set_print_implicits false;
     (match ret_ty with
      | Term.Kind -> ()
      | _ ->
        (* Print return type to a buffer so we can post-process *)
        let buf = Buffer.create 128 in
        let ppf_buf = Format.formatter_of_buffer buf in
        Format.fprintf ppf_buf "%a" print_term ret_ty;
        Format.pp_print_flush ppf_buf ();
        let ret_str = Buffer.contents buf in
        (* Apply @-prefix replacements for filled implicit args *)
        let ret_str = apply_explicit_replacements name ret_str in
        Format.fprintf ppf " : %s" ret_str);
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

  (* Print RHS with implicits off so unsolved metas become _ *)
  set_print_implicits false;
  Format.fprintf ppf " ↪ %a" print_term rule.Term.rhs;
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

(* Each encoded command: symbol declarations + rules, printed in order *)
type output_item = {
  oi_syms  : sym list;
  oi_rules : (sym * rule) list;
  oi_raw   : string;
}

let print_signature ppf ~prelude_module ~deps items =
  let open_deps =
    if deps = [] then [prelude_module] else deps
  in
  Format.fprintf ppf "require open %s;@.@."
    (String.concat " " open_deps);
  List.iter (fun item ->
    if item.oi_raw <> "" then
      Format.fprintf ppf "%s@." item.oi_raw;
    List.iter (print_symbol ppf) item.oi_syms;
    print_rules ppf item.oi_rules
  ) items

(* File operations *)
let rec mkdir_p dir =
  if not (Sys.file_exists dir) then begin
    mkdir_p (Filename.dirname dir);
    Sys.mkdir dir 0o755
  end

(* Build text replacements from alias table.
   E.g., "{|eo::String|}" → "Seq Char" *)
let alias_replacements () =
  let buf = Buffer.create 64 in
  let repls = ref [] in
  Hashtbl.iter (fun name target ->
    Buffer.clear buf;
    let ppf = Format.formatter_of_buffer buf in
    set_do_not_qualify true;
    Print.term ppf target;
    Format.pp_print_flush ppf ();
    set_do_not_qualify false;
    repls := (name, Buffer.contents buf) :: !repls
  ) alias_table;
  !repls

let write_lp_file filepath ~prelude_module ~deps items =
  let dir = Filename.dirname filepath in
  if dir <> "." && dir <> "" then mkdir_p dir;
  (* Separate alias rules (arity 0, head symbol is an alias) from other items *)
  let repls = alias_replacements () in
  let alias_names = List.map fst repls in
  let is_alias_rule (sym, rule) =
    rule.Term.arity = 0 && List.mem sym.Term.sym_name alias_names
  in
  let alias_items = ref [] in
  let other_items = List.map (fun item ->
    let aliases, others = List.partition is_alias_rule item.oi_rules in
    alias_items := aliases @ !alias_items;
    { item with oi_rules = others }
  ) items in
  (* Print main content to buffer for post-processing *)
  let buf = Buffer.create 4096 in
  let ppf = Format.formatter_of_buffer buf in
  print_signature ppf ~prelude_module ~deps other_items;
  Format.pp_print_flush ppf ();
  (* Post-process: replace alias names that Print.term inserts
     as implicit type arguments (not reachable by reduce_aliases) *)
  let content = Buffer.contents buf in
  let content = List.fold_left (fun s (name, replacement) ->
    let re = Str.regexp_string name in
    Str.global_replace re replacement s
  ) content repls in
  (* Append alias rules (not post-processed) *)
  let alias_buf = Buffer.create 256 in
  let alias_ppf = Format.formatter_of_buffer alias_buf in
  if !alias_items <> [] then
    print_rules alias_ppf !alias_items;
  Format.pp_print_flush alias_ppf ();
  let oc = open_out filepath in
  output_string oc content;
  output_string oc (Buffer.contents alias_buf);
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
      "cd %s && NO_COLOR=1 timeout --signal=KILL 3 lambdapi check -w %s 2>&1"
      (Filename.quote output_dir) (Filename.quote rel_path)
  in
  let ic  = Unix.open_process_in cmd in
  let buf = Buffer.create 256 in
  (try
     while true do Buffer.add_channel buf ic 1 done
   with End_of_file -> ());
  let status = Unix.close_process_in ic in
  (* Get absolute path of output_dir for stripping *)
  let abs_output_dir =
    if Filename.is_relative output_dir then
      Filename.concat (Sys.getcwd ()) output_dir
    else output_dir
  in
  let output =
    Buffer.contents buf
    |> String.trim
    (* Remove ANSI escape codes *)
    |> Str.global_replace (Str.regexp "\027\\[[0-9;]*m") ""
    (* Remove "Start checking ..." line *)
    |> Str.global_replace (Str.regexp "Start checking [^\n]*\n?") ""
    (* Strip output_dir prefix from paths, keeping relative path *)
    |> Str.global_replace (Str.regexp_string (abs_output_dir ^ "/")) ""
    (* Strip filename from location brackets, e.g. [foo/Bar.lp:27:5-102] -> [27:5-102] *)
    |> Str.global_replace (Str.regexp "\\[[^]]*\\.lp:\\([0-9][^]]*\\)\\]") "[\\1]"
    |> String.trim
  in
  (* Add newline after first location bracket: "[27:5-102] msg" -> "[27:5-102]\n  msg" *)
  let output =
    match Str.search_forward (Str.regexp "\\[[0-9][^]]*\\] ") output 0 with
    | n ->
      let matched = Str.matched_string output in
      let before = String.sub output 0 n in
      let bracket = String.sub matched 0 (String.length matched - 1) in (* drop trailing space *)
      let after = String.sub output (n + String.length matched) (String.length output - n - String.length matched) in
      before ^ bracket ^ "\n" ^ after
    | exception Not_found -> output
  in
  match status with
  | Unix.WEXITED 0   -> Check_ok
  | Unix.WEXITED 124 -> Check_error "timeout"
  | _                -> Check_error output
