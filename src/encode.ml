(* encode.ml
   Eunoia to LambdaPi encoding *)

module EO = Syntax_eo
open Api_lp

(* Re-exports for main.ml *)
let verbose     = Api_lp.verbose
let set_verbose = Api_lp.set_verbose

(* Error handling with context *)
let fail msg = Api_lp.fail msg
let failf fmt = Api_lp.failf fmt

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
    fail "Empty arrow type"
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
      | None ->
        let ctx_vars = List.map (fun (v, _, _) -> base_name v) ctx in
        failf "enc_arrow: variable `%s` not in context. Available: [%s]"
          s (String.concat ", " ctx_vars)
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

(* Rule encoding for declare-rule *)

(* Get the Proof symbol from prelude *)
let proof_sym () = find "Proof"

(* Build Proof(t) application *)
let mk_proof t = mk_Appl (mk_Symb (proof_sym ()), t)

(* Encode a declare-rule.

   For rules with :args, we generate:

     symbol <name>_aux [<type_params>] : τ T1 → ... → τ Tn → TYPE;
     rule <name>_aux <pattern1> ... <patternN>
       ↪ Proof <prem1> → ... → Proof <premM> → Proof <conclusion>;

     symbol <name> [<type_params>] :
       Π x1 : τ T1, ... Π xn : τ Tn, <name>_aux x1 ... xn;

   For rules without :args (only :premises), we generate:

     symbol <name> [<type_params>] (p1 : τ T1) ... :
       Proof <prem1> → ... → Proof <premM> → Proof <conclusion>;
*)
let enc_rule str ps assm prems args reqs conc =
  (* Ignore assumption for now - used for scope rules with assume-push/step-pop *)
  let _ = assm in
  (* Ignore reqs for now - should wrap conclusion in eo::requires *)
  let _ = reqs in

  (* Handle :premise-list - extract the pattern from eo::premise_list wrapper.
     :premise-list F and means the rule takes an arbitrary number of premises,
     which are combined using 'and' at proof time. For the encoding, we just
     use the pattern F as a single premise. *)
  let prems = List.map (function
    | EO.Apply ("eo::premise_list", [pattern; _op]) -> pattern
    | p -> p) prems
  in

  let ctx, _ = enc_params ps in

  (* Helper: build Proof p1 → Proof p2 → ... → Proof conclusion *)
  let build_proof_arrow prems conc_term =
    let conc_proof = mk_proof conc_term in
    List.fold_right
      (fun prem acc ->
         let prem_proof = mk_proof prem in
         mk_Prod (prem_proof, bind_var (new_var "_") acc))
      prems conc_proof
  in

  (* Check if an arg is a simple variable reference (not a pattern) *)
  let is_simple_arg = function
    | EO.Symbol s -> EO.prm_mem s ps  (* It's a parameter reference *)
    | _ -> false
  in

  (* Check if ALL args are simple variable references *)
  let all_args_simple = List.for_all is_simple_arg args in

  if args = [] || all_args_simple then begin
    (* No :args - simple rule with just premises and conclusion *)
    (* Encode premises and conclusion *)
    let prems_enc = List.map (fun p -> enc_term ctx p |> resolve_term ~ctx) prems in
    let conc_enc = enc_term ctx conc |> resolve_term ~ctx in

    (* Build the type: Proof prem1 → ... → Proof premN → Proof conclusion *)
    let body_ty = build_proof_arrow prems_enc conc_enc in

    (* Find free type variables for implicit params *)
    let free_vars = Api_lp.LibTerm.free_vars body_ty in
    let impl_ctx =
      List.filter (fun (v, _, _) -> Core.Term.VarSet.mem v free_vars) ctx
    in
    let impl = List.map (fun _ -> true) impl_ctx in
    let ty, _ = Core.Ctxt.to_prod impl_ctx body_ty in

    let sym = add_constant ~impl (unique_name str) ty in
    { sym = Some sym; rules = []; after_rules = [] }

  end else begin
    (* Has :args - need auxiliary symbol with rewrite rule *)

    (* Create context for encoding args - need all params *)
    let arg_ctx, _ = enc_params ps in

    (* Infer the type of each arg by encoding and using LambdaPi's type inference.
       We encode the arg term, then use Infer to get its type. *)
    let infer_arg_type arg =
      let encoded = enc_term arg_ctx arg in
      let resolved = resolve_term ~ctx:arg_ctx encoded in
      (* Use LambdaPi's infer to get the type *)
      let prob = Core.Term.new_problem () in
      match Core.Infer.infer_noexn prob arg_ctx resolved with
      | Some (_, ty) ->
        (* ty is the LambdaPi type (e.g., τ U). We want just U (the Set). *)
        (* If ty = τ X, extract X. Otherwise use ty as-is. *)
        un_tau ty
      | None ->
        (* Fallback: use a placeholder *)
        failf "Cannot infer type of arg: %s" (EO.term_str arg)
    in

    let arg_lp_types = List.map infer_arg_type args in

    (* Build the _aux symbol type: τ T1 → τ T2 → ... → TYPE *)
    let aux_body_ty =
      List.fold_right
        (fun arg_ty acc ->
           let ty_enc = tau_of arg_ty in
           mk_Prod (ty_enc, bind_var (new_var "_") acc))
        arg_lp_types
        (mk_Type)
    in

    (* Find implicit type params for _aux *)
    let aux_free_vars = Api_lp.LibTerm.free_vars aux_body_ty in
    let aux_impl_ctx =
      List.filter (fun (v, _, _) -> Core.Term.VarSet.mem v aux_free_vars) arg_ctx
    in
    let aux_impl = List.map (fun _ -> true) aux_impl_ctx in
    let aux_ty, _ = Core.Ctxt.to_prod aux_impl_ctx aux_body_ty in

    let aux_name = unique_name (str ^ "_aux") in
    let aux_sym = add_sequential ~impl:aux_impl aux_name aux_ty in

    (* Build the rewrite rule for _aux using enc_case.
       We construct synthetic Eunoia terms:
         LHS: (aux_name arg1 arg2 ...)
         RHS: a term that will encode to Proof prem1 → ... → Proof conclusion

       For the RHS, we build the proof arrow directly since there's no
       Eunoia syntax for Proof types. *)

    (* Build LHS as an Eunoia Apply term *)
    let lhs_eo = EO.Apply (aux_name, args) in

    (* For RHS, we need to encode it specially since Proof is not in Eunoia.
       We'll encode the premises and conclusion, then build the arrow. *)
    let enc t = t
      |> enc_term arg_ctx
      |> resolve_term ~debug:true ~ctx:arg_ctx
      |> bind_pvars arg_ctx
    in

    let prems_enc = List.map enc prems in
    let conc_enc = enc conc in
    let rhs = build_proof_arrow prems_enc conc_enc in

    (* For LHS, use enc_case's encoding pattern *)
    let l = lhs_eo
      |> enc_term arg_ctx
      |> resolve_term ~debug:true ~ctx:arg_ctx
      |> bind_pvars arg_ctx
    in
    let _, lhs_args = Core.Term.get_args l in

    let names = List.rev_map (fun (v, _, _) -> base_name v) arg_ctx |> Array.of_list in
    let vars_nb = List.length arg_ctx in

    let aux_rule : rule = {
      lhs = lhs_args;
      rhs;
      arity = List.length lhs_args;
      arities = Array.make vars_nb 0;
      vars_nb;
      xvars_nb = 0;
      names;
      rule_pos = None;
    } in

    (* Build the main symbol type:
       Π x1 : τ T1, ... Π xn : τ Tn, <name>_aux x1 ... xn *)

    (* Create fresh variables for the Π-bound args *)
    let arg_vars = List.mapi (fun i _ -> new_var (Printf.sprintf "x%d" (i + 1))) arg_lp_types in

    (* Build _aux applied to the arg variables.
       Use enc_sym to insert placeholders for implicit type parameters. *)
    let aux_applied =
      List.fold_left
        (fun acc v -> mk_Appl (acc, mk_Vari v))
        (enc_sym aux_sym)
        arg_vars
    in

    (* Build Π x1 : τ T1, ... Π xn : τ Tn, aux_applied *)
    let main_body_ty =
      List.fold_right2
        (fun arg_ty v acc ->
           let ty_enc = tau_of arg_ty in
           mk_Prod (ty_enc, bind_var v acc))
        arg_lp_types arg_vars aux_applied
    in

    (* Find implicit type params for main symbol *)
    let main_free_vars = Api_lp.LibTerm.free_vars main_body_ty in
    let main_impl_ctx =
      List.filter (fun (v, _, _) -> Core.Term.VarSet.mem v main_free_vars) arg_ctx
    in
    let main_impl = List.map (fun _ -> true) main_impl_ctx in
    let main_ty, _ = Core.Ctxt.to_prod main_impl_ctx main_body_ty in

    let main_sym = add_constant ~impl:main_impl (unique_name str) main_ty in

    { sym = Some main_sym;
      rules = [(aux_sym, aux_rule)];
      after_rules = [] }
  end

(* Encode an assume command.
   (assume s F) becomes: symbol s : Proof F; *)
let enc_assume str formula =
  let ctx = empty_ctxt in
  let formula_enc = enc_term ctx formula |> resolve_term ~ctx in
  let ty = mk_proof formula_enc in
  let sym = add_constant ~impl:[] (unique_name str) ty in
  { sym = Some sym; rules = []; after_rules = [] }

(* Encode a step command.
   (step s F :rule r :premises (p1 ... pn) :args (a1 ... am))
   becomes: symbol s ≔ r p1 ... pn a1 ... am; (with optional : Proof F) *)
let enc_step str rule_name premises args conc_opt =
  let ctx = empty_ctxt in
  (* Build the application: (rule_name premise1 ... premiseN arg1 ... argM) *)
  let rule_sym = get_sym rule_name in
  let head = enc_sym rule_sym in
  (* Encode premises (which are proof term references) *)
  let prems_enc = List.map (fun p -> enc_term ctx p |> resolve_term ~ctx) premises in
  (* Encode args *)
  let args_enc = List.map (fun a -> enc_term ctx a |> resolve_term ~ctx) args in
  (* Build the full application *)
  let body_raw = List.fold_left (fun acc arg -> mk_Appl (acc, arg)) head (prems_enc @ args_enc) in
  (* Determine expected type if conclusion provided, and resolve body with it *)
  let body, expected_ty = match conc_opt with
    | Some conc ->
      let conc_enc = enc_term ctx conc |> resolve_term ~ctx in
      let exp_ty = mk_proof conc_enc in
      (* Resolve body with expected type to help unification *)
      let body_resolved = resolve_term ~ctx ~expected_ty:exp_ty body_raw in
      (body_resolved, Some exp_ty)
    | None ->
      (resolve_term ~ctx body_raw, None)
  in
  let sym = add_definition ~impl:[] (unique_name str) expected_ty body in
  { sym = Some sym; rules = []; after_rules = [] }

let enc_symbol name = function
  | EO.Decl (ps, ty, attr) ->
    enc_decl name ps ty attr
  | EO.Defn (ps, body, ty_opt) ->
    enc_defn name ps body ty_opt
  | EO.Prog (ps, doms, ran, cases) ->
    enc_prog name ps doms ran cases
  | EO.Ltrl (cat, ty) ->
    enc_ltrl cat ty
  | EO.Rule (ps, assm, prems, args, reqs, conc) ->
    enc_rule name ps assm prems args reqs conc
  | EO.Assume formula ->
    enc_assume name formula
  | EO.Step (rule_name, premises, args, conc_opt) ->
    enc_step name rule_name premises args conc_opt

(* Signature encoding result *)
type enc_sig_result = {
  rules : (sym * rule) list;
  after_rules_map : (sym, (sym * rule) list) Hashtbl.t;
  errors : (string * string) list;  (* (symbol_name, error_message) *)
}

(* Signature encoding *)
let enc_signature sig_ =
  reset_overloads ();
  let all_rules = ref [] in
  (* after_rules_map: symbol -> list of rules to print after that symbol *)
  let after_rules_map = Hashtbl.create 16 in
  let errors = ref [] in
  List.iter
    (fun (name, sym) ->
       try
         set_current_symbol name;
         set_current_phase "encode";
         let result = enc_symbol name sym in
         all_rules := !all_rules @ result.rules;
         (* Associate after_rules with the symbol that was created *)
         (match result.sym with
          | Some sym when result.after_rules <> [] ->
            Hashtbl.add after_rules_map sym result.after_rules
          | _ -> ())
       with
       | Failure msg ->
         errors := (name, msg) :: !errors
       | exn ->
         errors := (name, Printexc.to_string exn) :: !errors)
    sig_;
  set_current_symbol "";
  set_current_phase "";
  { rules = !all_rules; after_rules_map; errors = List.rev !errors }
