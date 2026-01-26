(* encode.ml
   Eunoia to LambdaPi encoding *)

module EO = Syntax_eo
open Api_lp

(* Re-exports for main.ml *)
let verbose     = Api_lp.verbose
let set_verbose = Api_lp.set_verbose

(* Overload management *)
let overload_counts : (string, int) Hashtbl.t =
  Hashtbl.create 32

let lit_type_substitutions : (string, string) Hashtbl.t =
  Hashtbl.create 8

(* Nullary aliases: name -> expansion term (persisted across modules) *)
let nullary_aliases : (string, EO.term) Hashtbl.t =
  Hashtbl.create 16

let reset_overloads () =
  Hashtbl.clear overload_counts;
  (* Note: do NOT clear nullary_aliases - they persist across modules *)
  reset_symbol_storage ()

(* Get a unique name for potentially overloaded symbols *)
let unique_name name =
  let escaped = esc name in
  match Hashtbl.find_opt overload_counts escaped with
  | None ->
    Hashtbl.add overload_counts escaped 1;
    escaped
  | Some n ->
    Hashtbl.replace overload_counts escaped (n + 1);
    Printf.sprintf "%s_%d" escaped n

let reset () =
  Api_lp.reset ();
  Hashtbl.clear lit_type_substitutions;
  reset_overloads ()

(* Literal encoding *)
let enc_literal = function
  | Literal.Numeral n ->
    enc_int n
  | Literal.Decimal d ->
    mk_Symb (ghost_sym (string_of_float d))
  | Literal.Rational (num, den) ->
    add_args
      (mk_Symb (find "{|eo::mkrat|}"))
      [enc_int num; enc_int den]
  | Literal.String s ->
    mk_Symb (ghost_sym ("\"" ^ s ^ "\""))
  | Literal.Binary b ->
    (* Convert binary literal #bXXX to (@bv value width) *)
    let bits = String.sub b 2 (String.length b - 2) in (* Remove #b prefix *)
    let width = String.length bits in
    let value = int_of_string ("0b" ^ bits) in
    add_args
      (mk_Symb (find "{|@bv|}"))
      [enc_int value; enc_int width]
  | Literal.Hexadecimal h ->
    (* h already includes the #x prefix from lexer *)
    mk_Symb (ghost_sym h)

(* Term encoding *)
let rec enc_term ctx = function
  | EO.Symbol "Type" ->
    eo_type ()
  | EO.Symbol s ->
    (match ctxt_find ctx (esc s) with
     | Some v -> mk_Vari v
     | None ->
       (* Check for nullary alias first *)
       match Hashtbl.find_opt nullary_aliases s with
       | Some expansion -> enc_term ctx expansion
       | None -> enc_sym (get_sym s))
  | EO.Literal lit ->
    enc_literal lit
  | EO.Apply ("->", args) ->
    enc_arrow ctx args
  | EO.Apply (("as" | "eo::as"), [ty; tm]) ->
    eo_as (enc_term ctx ty) (enc_term ctx tm)
  | EO.Apply ("_", [f; x]) ->
    hol_app (enc_term ctx f) (enc_term ctx x)
  | EO.Apply (s, ts) ->
    add_args
      (enc_sym (get_sym (esc s)))
      (List.map (enc_term ctx) ts)
  | EO.Bind ("eo::define", xs, body) ->
    (* Build context with all let-bound variables first *)
    let vars =
      List.map (fun (s, _) -> (s, new_var (esc s))) xs
    in
    let ctx' =
      List.fold_left
        (fun c (s, v) -> ctxt_add c v (mk_Plac false))
        ctx vars
    in
    (* Now encode with extended context and wrap in let-bindings *)
    List.fold_right2
      (fun (_, t) (_, v) acc ->
         Core.Term.mk_LLet
           (mk_Plac false,
            enc_term ctx t,
            bind_var v acc))
      xs vars (enc_term ctx' body)

and enc_arrow ctx = function
  | [] ->
    failwith "Empty arrow type"
  | [t] ->
    enc_term ctx t
  | EO.Apply ("eo::quote", [EO.Symbol s]) :: rest ->
    (* Dependent arrow: (eo_type_of_s) ⤳d (λ s': type_of_s, ..rest..)
       where type_of_s is the type of s (looked up from context, i.e., τ T),
       eo_type_of_s is the unwrapped Eunoia type (i.e., T),
       and rest is encoded with s shadowed by s'.
       E.g., for T : Type, we get {|eo::Type|} ⤳d (λ T: Set, ...) *)
    let s_esc = esc s in
    let type_of_s =
      match List.find_opt (fun (v, _, _) -> base_name v = s_esc) ctx with
      | Some (_, ty, _) -> ty
      | None -> failwith ("enc_arrow: variable not in context: " ^ s)
    in
    (* Unwrap τ from type_of_s to get the Eunoia type for ⤳d's first arg *)
    let eo_type_of_s = un_tau type_of_s in
    let v = new_var s_esc in
    let ctx' = ctxt_add ctx v type_of_s in
    let body = enc_arrow ctx' rest in
    let lam = mk_Abst (type_of_s, bind_var v body) in
    hol_dep_arrow eo_type_of_s lam
  | t :: rest ->
    hol_arrow (enc_term ctx t) (enc_arrow ctx rest)

(* Parameter encoding *)
let enc_params ps =
  let ctx, impl =
    List.fold_left
      (fun (ctx, acc) (str, ty, atts) ->
         let v = new_var (esc str) in
         (* Type parameters (T : Type) have type Set (= τ {|eo::Type|}) *)
         let ty' = tau_of (enc_term ctx ty) in
         let ctx' = ctxt_add ctx v ty' in
         let is_impl = List.mem EO.Implicit atts in
         (ctx', is_impl :: acc))
      (empty_ctxt, [])
      ps
  in
  (* Context is built in reverse order (ctxt_add prepends), which is what
     ctxt_to_prod/ctxt_to_abst expect (they use fold_left, wrapping first
     element as innermost binder, producing Π p_n. ... Π p_1. body).

     impl is accumulated in reverse order [p_n_impl; ...; p_1_impl], but
     the final type has params in original order (p_1 outermost), so we
     must reverse impl to match: [p_1_impl; ...; p_n_impl]. *)
  (ctx, List.rev impl)

(* Constant encoding *)
type enc_result = {
  sym   : sym option;
  rules : (sym * rule) list;
  after_rules : (sym * rule) list;  (* Rules to print immediately after sym *)
}

let empty_result = { sym = None; rules = []; after_rules = [] }

let enc_decl str ps ty _attr =
  let ctx, impl = enc_params ps in
  let body_ty = tau_of (enc_term ctx ty) in
  let ty', _ = ctxt_to_prod ctx body_ty in
  (* Don't wrap in tau_of - ctxt_to_prod already produces a TYPE via Π-binders,
     and the body is already wrapped in τ. *)
  { sym   = Some (add_constant ~impl (unique_name str) ty');
    rules = []; after_rules = [] }

let enc_defn str ps tm ty_opt =
  match ps with
  | [] ->
    (* Record nullary alias for later expansion (persists across modules) *)
    Hashtbl.replace nullary_aliases str tm;
    empty_result
  | _ ->
    let ctx, impl = enc_params ps in
    let body_raw = enc_term ctx tm in
    let expected_ty = Option.map (fun ty -> tau_of (enc_term ctx ty)) ty_opt in
    let body = resolve_term ~ctx ?expected_ty body_raw in
    let tm' = ctxt_to_abst ctx body in
    { sym   = Some (add_definition ~impl (unique_name str) None tm');
      rules = []; after_rules = [] }

(* Rule encoding for programs *)

(* Convert variables in a term to pattern variables.
   Takes a context (from enc_params) and replaces Vari nodes with Patt nodes. *)
let bind_pvars ctx term =
  (* Build mapping from variable name to index *)
  let var_indices =
    List.mapi (fun i (v, _, _) -> (base_name v, i)) ctx
    |> List.rev  (* ctx is reversed, so reverse to get original order *)
  in
  let rec go = function
    | Core.Term.Vari v ->
      let name = base_name v in
      (match List.find_opt (fun (n, _) -> n = name) var_indices with
       | Some (_, idx) -> mk_Patt (Some idx, name, [||])
       | None -> mk_Vari v)
    | Core.Term.Symb s ->
      let name = s.Core.Term.sym_name in
      (match List.find_opt (fun (n, _) -> n = name) var_indices with
       | Some (_, idx) -> mk_Patt (Some idx, name, [||])
       | None -> mk_Symb s)
    | Core.Term.Meta (m, ts) ->
      (* If meta is unsolved, convert to wildcard for LambdaPi to elaborate *)
      if Option.is_none Timed.(!(m.Core.Term.meta_value)) then
        mk_Plac false
      else
        Core.Term.mk_Meta (m, Array.map go ts)
    | Core.Term.Appl (t1, t2) ->
      mk_Appl (go t1, go t2)
    | Core.Term.Abst (ty, b) ->
      let v, body = unbind b in
      mk_Abst (go ty, bind_var v (go body))
    | Core.Term.Prod (ty, b) ->
      let v, body = unbind b in
      mk_Prod (go ty, bind_var v (go body))
    | Core.Term.LLet (ty, t, b) ->
      let v, body = unbind b in
      Core.Term.mk_LLet (go ty, go t, bind_var v (go body))
    | t -> t
  in
  go term

(* Encode a program case as a rewrite rule *)
let enc_case ctx sym (t1, t2 : EO.term * EO.term) =
  let enc t = t
    |> enc_term ctx
    |> resolve_term ~debug:true ~ctx
    |> bind_pvars ctx
  in

  let l, rhs = enc t1, enc t2 in
  let _,lhs = Core.Term.get_args l in
  let names = List.rev_map (fun (v, _, _) -> base_name v) ctx |> Array.of_list in
  let vars_nb = List.length ctx in
  let rule : rule = {
    lhs;
    rhs;
    arity = List.length lhs;
    arities = Array.make vars_nb 0;
    vars_nb;
    xvars_nb = 0;
    names;
    rule_pos = None;
  } in
  (sym, rule)

(* Deduplicate while preserving order of first occurrence *)
let dedup_params ps =
  let seen = Hashtbl.create (List.length ps) in
  List.filter (fun (name, _, _) ->
    if Hashtbl.mem seen name then false
    else (Hashtbl.add seen name (); true))
  ps

let enc_prog str ps doms ran cases =
  let ctx, _ = enc_params ps in
  let ty_raw = EO.Apply ("->", doms @ [ran]) in
  (* Use all program parameters for encoding context *)
  let ty_ctx, _ = enc_params ps in
  (* Encode the type - this processes eo::quote into dependent arrows *)
  let body_ty_raw = tau_of (enc_term ty_ctx ty_raw) in
  (* Resolve placeholders with the full context *)
  let body_ty = resolve_term ~ctx:ty_ctx body_ty_raw in
  (* Find which variables from ty_ctx are free in the encoded type.
     These become the implicit parameters that need Π-binding. *)
  let free_vars = Api_lp.LibTerm.free_vars body_ty in
  let impl_ctx =
    List.filter (fun (v, _, _) -> Core.Term.VarSet.mem v free_vars) ty_ctx
  in
  let impl = List.map (fun _ -> true) impl_ctx in
  let ty, _ = Core.Ctxt.to_prod impl_ctx body_ty in
  let sym = add_sequential ~impl (unique_name str) ty in

  (* Encode each case as a rule using the parameter context *)
  let rules =
    List.filter_map (fun (lhs, rhs) ->
      try Some (enc_case ctx sym (lhs, rhs))
      with Failure msg ->
        Printf.eprintf "Warning: %s: rule encoding failed: %s\n%!" str msg;
        None)
    cases
  in
  { sym = Some sym; rules; after_rules = [] }

(* Create a simple rule with no pattern variables: sym arg1 arg2 ... ↪ rhs *)
let make_rule sym lhs rhs =
  let rule : rule = {
    lhs;
    rhs;
    arity = List.length lhs;
    arities = [||];
    vars_nb = 0;
    xvars_nb = 0;
    names = [||];
    rule_pos = None;
  } in
  (sym, rule)

let enc_ltrl cat ty =
  (match ty with
   | EO.Symbol ty_name -> EO.set_lit_type cat ty_name
   | _ -> ());

  (* Determine the eo:: type for this literal category *)
  let eo_type_name = match cat with
    | Literal.NUM -> Some "{|eo::Int|}"
    | Literal.DEC | Literal.RAT -> Some "{|eo::Rat|}"
    | Literal.STR -> Some "{|eo::String|}"
    | _ -> None
  in

  match ty, eo_type_name with
  | EO.Symbol target_type, Some eo_type ->
    Hashtbl.replace lit_type_substitutions target_type eo_type;

    (* Get the symbols we need *)
    let eo_type_sym = find eo_type in
    let target_term = enc_term empty_ctxt ty in
    let tau_sym = tau () in

    (* Create a rewrite rule: τ target_type ↪ τ eo_type
       e.g., τ Int ↪ ℤ (since τ {|eo::Int|} ↪ ℤ already exists)
       This makes values of SMT type have the same LambdaPi type as internal eo:: type *)
    let tau_eo = mk_Appl (mk_Symb tau_sym, mk_Symb eo_type_sym) in
    let tau_rule = make_rule tau_sym [target_term] tau_eo in

    { sym = None;
      rules = [tau_rule];
      after_rules = [] }

  | _ ->
    empty_result

let enc_const name = function
  | EO.Decl (ps, ty, attr) ->
    enc_decl name ps ty attr
  | EO.Defn (ps, body, ty_opt) ->
    enc_defn name ps body ty_opt
  | EO.Prog (ps, doms, ran, cases) ->
    enc_prog name ps doms ran cases
  | EO.Ltrl (cat, ty) ->
    enc_ltrl cat ty
  | EO.Rule _ ->
    empty_result

(* Signature encoding *)
let enc_signature sig_ =
  reset_overloads ();
  let all_rules = ref [] in
  (* after_rules_map: symbol -> list of rules to print after that symbol *)
  let after_rules_map = Hashtbl.create 16 in
  List.iter
    (fun (name, const) ->
       try
         set_current_symbol name;
         let result = enc_const name const in
         all_rules := !all_rules @ result.rules;
         (* Associate after_rules with the symbol that was created *)
         (match result.sym with
          | Some sym when result.after_rules <> [] ->
            Hashtbl.add after_rules_map sym result.after_rules
          | _ -> ())
       with Failure msg ->
         Printf.eprintf "Warning: %s: encoding failed: %s\n%!" name msg)
    sig_;
  set_current_symbol "";
  (!all_rules, after_rules_map)
