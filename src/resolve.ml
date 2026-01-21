(* ============================================================
   Type Resolution for Syntax_lp

   This module performs type inference and resolution on LambdaPi terms:
   1. Instantiate implicit parameters with fresh metavariables
   2. Generate type constraints from function application
   3. Solve constraints via unification
   4. Substitute solved metavariables back into terms

   Pattern variables are handled separately by bind_pvars.
   ============================================================ *)

module LP = Syntax_lp

module L = List

(* ============================================================
   Symbol Context
   ============================================================ *)

(* A symbol entry contains the symbol's parameters and type *)
type symbol_entry = {
  sym_name : string;
  sym_params : LP.param list;    (* all parameters (implicit and explicit) *)
  sym_type : LP.term option;     (* return type, if known *)
}

(* The typing context *)
type context = {
  ctx_symbols : (string, symbol_entry) Hashtbl.t;
  ctx_locals : (string * LP.term) list;  (* local variable types *)
}

let create_context () : context = {
  ctx_symbols = Hashtbl.create 64;
  ctx_locals = [];
}

let add_symbol (ctx : context) (name : string) (params : LP.param list) (ty : LP.term option) : unit =
  Hashtbl.replace ctx.ctx_symbols name {
    sym_name = name;
    sym_params = params;
    sym_type = ty;
  }

let lookup_symbol (ctx : context) (name : string) : symbol_entry option =
  Hashtbl.find_opt ctx.ctx_symbols name

let extend_local (ctx : context) (name : string) (ty : LP.term) : context =
  { ctx with ctx_locals = (name, ty) :: ctx.ctx_locals }

let lookup_local (ctx : context) (name : string) : LP.term option =
  L.assoc_opt name ctx.ctx_locals

(* ============================================================
   Type Definitions
   ============================================================ *)

type constraint_ = LP.term * LP.term
type constraints = constraint_ list

(* Result of inferring a term: the elaborated term, its type, and constraints *)
type infer_result = {
  term : LP.term;
  ty : LP.term;
  constrs : constraints;
}

(* ============================================================
   Prelude Builtins
   ============================================================ *)

let set_ty = LP.Var "Set"
let tau ty = LP.App (LP.Var "τ", ty)
let arrow a b = LP.App (LP.App (LP.Var "⤳", a), b)

(* Add core Prelude symbols to context *)
let add_prelude_builtins (ctx : context) : unit =
  (* APP [a : Set] [b : Set] : τ (a ⤳ b) → τ a → τ b *)
  add_symbol ctx "eo.APP" [
    ("a", set_ty, LP.Implicit);
    ("b", set_ty, LP.Implicit);
  ] (Some (LP.Arrow (
    tau (arrow (LP.Var "a") (LP.Var "b")),
    LP.Arrow (tau (LP.Var "a"), tau (LP.Var "b"))
  )));

  (* List__cons [T : Set] : τ (T ⤳ List ⤳ List) *)
  add_symbol ctx "eo.List__cons" [
    ("T", set_ty, LP.Implicit);
  ] (Some (tau (arrow (LP.Var "T") (arrow (LP.Var "eo.List") (LP.Var "eo.List")))));

  (* eq [T : Set] [S : Set] : τ (T ⤳ S ⤳ Bool) *)
  add_symbol ctx "eo.eq" [
    ("T", set_ty, LP.Implicit);
    ("S", set_ty, LP.Implicit);
  ] (Some (tau (arrow (LP.Var "T") (arrow (LP.Var "S") (LP.Var "Bool")))));

  (* ite [U : Set] [T : Set] : τ Bool → τ U → τ T → τ (?? b U T) *)
  (* Simplified: we treat return type as a fresh metavar *)
  add_symbol ctx "eo.ite" [
    ("U", set_ty, LP.Implicit);
    ("T", set_ty, LP.Implicit);
  ] None;

  (* gt [T1 : Set] [T2 : Set] : τ (T1 ⤳ T2 ⤳ Bool) *)
  add_symbol ctx "eo.gt" [
    ("T1", set_ty, LP.Implicit);
    ("T2", set_ty, LP.Implicit);
  ] (Some (tau (arrow (LP.Var "T1") (arrow (LP.Var "T2") (LP.Var "Bool")))));

  (* is_var [T : Set] : τ (T ⤳ Bool) *)
  add_symbol ctx "eo.is_var" [
    ("T", set_ty, LP.Implicit);
  ] (Some (tau (arrow (LP.Var "T") (LP.Var "Bool"))));

  (* cmp [T : Set] [U : Set] : τ (T ⤳ U ⤳ Bool) *)
  add_symbol ctx "eo.cmp" [
    ("T", set_ty, LP.Implicit);
    ("U", set_ty, LP.Implicit);
  ] (Some (tau (arrow (LP.Var "T") (arrow (LP.Var "U") (LP.Var "Bool")))));

  (* requires [T : Set] [U : Set] [V : Set] : τ T → τ U → τ V → τ V *)
  add_symbol ctx "eo.requires" [
    ("T", set_ty, LP.Implicit);
    ("U", set_ty, LP.Implicit);
    ("V", set_ty, LP.Implicit);
  ] (Some (LP.Arrow (tau (LP.Var "T"),
           LP.Arrow (tau (LP.Var "U"),
           LP.Arrow (tau (LP.Var "V"), tau (LP.Var "V"))))));

  (* typeof [T : Set] : τ (T ⤳ Type) *)
  add_symbol ctx "eo.typeof" [
    ("T", set_ty, LP.Implicit);
  ] (Some (tau (arrow (LP.Var "T") (LP.Var "eo.Type"))));

  (* cons [U : Set] [T : Set] : τ ((U ⤳ T ⤳ T) ⤳ U ⤳ T ⤳ T) *)
  add_symbol ctx "eo.cons" [
    ("U", set_ty, LP.Implicit);
    ("T", set_ty, LP.Implicit);
  ] None;

  (* add, mul, neg, etc. *)
  add_symbol ctx "eo.add" [("T1", set_ty, LP.Implicit); ("T2", set_ty, LP.Implicit)] None;
  add_symbol ctx "eo.mul" [("T1", set_ty, LP.Implicit); ("T2", set_ty, LP.Implicit)] None;
  add_symbol ctx "eo.neg" [("T", set_ty, LP.Implicit)] None

(* ============================================================
   Instantiation
   ============================================================ *)

(* Instantiate a symbol's implicit parameters with fresh metavariables.
   Returns the term with metavar assignments and a substitution for the type. *)
let instantiate_symbol (entry : symbol_entry) : LP.term * (string * LP.term) list =
  let implicit_params = L.filter (fun (_, _, attr) -> attr = LP.Implicit) entry.sym_params in
  if implicit_params = [] then
    (LP.Var entry.sym_name, [])
  else
    let assigns = L.map (fun ((name, ty, attr) as param) ->
      let mv = LP.fresh_mvar () in
      (param, mv)
    ) implicit_params in
    let subst = L.map (fun ((name, _, _), mv) -> (name, mv)) assigns in
    (LP.Const (entry.sym_name, assigns), subst)

(* Apply a substitution to a term (for type parameter substitution) *)
let rec subst_vars (s : (string * LP.term) list) (t : LP.term) : LP.term =
  match t with
  | LP.Var x -> (match L.assoc_opt x s with Some t' -> t' | None -> t)
  | LP.Const (name, assigns) ->
    LP.Const (name, L.map (fun (p, arg) -> (p, subst_vars s arg)) assigns)
  | LP.App (f, x) -> LP.App (subst_vars s f, subst_vars s x)
  | LP.Arrow (a, b) -> LP.Arrow (subst_vars s a, subst_vars s b)
  | LP.Bind (binder, params, body) ->
    let params' = L.map (fun (n, ty, attr) -> (n, subst_vars s ty, attr)) params in
    let bound_names = L.map (fun (n, _, _) -> n) params in
    let s' = L.filter (fun (x, _) -> not (L.mem x bound_names)) s in
    LP.Bind (binder, params', subst_vars s' body)
  | LP.Let (x, e, body) ->
    let s' = L.filter (fun (y, _) -> y <> x) s in
    LP.Let (x, subst_vars s e, subst_vars s' body)
  | LP.MVar _ | LP.PVar _ | LP.Lit _ -> t

(* ============================================================
   Type Inference
   ============================================================ *)

(* Infer the type of a term, generating constraints *)
let rec infer (ctx : context) (t : LP.term) : infer_result =
  match t with
  (* Literals - assign appropriate types *)
  | LP.Lit lit ->
    let ty = match lit with
      | Literal.Numeral _ -> tau (LP.Var "eo.<int>")
      | Literal.Rational _ -> tau (LP.Var "eo.<rat>")
      | Literal.String _ -> tau (LP.Var "eo.<str>")
      | _ -> LP.fresh_mvar ()  (* Other literals get fresh type *)
    in
    { term = t; ty; constrs = [] }

  (* Variables - look up type or use fresh metavar *)
  | LP.Var name ->
    begin match lookup_local ctx name with
    | Some ty -> { term = t; ty; constrs = [] }
    | None ->
      match lookup_symbol ctx name with
      | Some entry ->
        let (term', param_subst) = instantiate_symbol entry in
        let ty = match entry.sym_type with
          | Some ty -> subst_vars param_subst ty
          | None -> LP.fresh_mvar ()
        in
        { term = term'; ty; constrs = [] }
      | None ->
        (* Unknown symbol - use fresh type metavar *)
        { term = t; ty = LP.fresh_mvar (); constrs = [] }
    end

  (* Constants with assignments - already instantiated *)
  | LP.Const (name, assigns) ->
    (* Recursively infer types of assignment args *)
    let (assigns', constrs) = L.fold_left (fun (acc_assigns, acc_cs) (param, arg) ->
      let res = infer ctx arg in
      (acc_assigns @ [(param, res.term)], acc_cs @ res.constrs)
    ) ([], []) assigns in
    let term' = LP.Const (name, assigns') in
    (* Look up the symbol's type and substitute *)
    let ty = match lookup_symbol ctx name with
      | Some entry ->
        let param_subst = L.map (fun ((pname, _, _), arg) -> (pname, arg)) assigns' in
        begin match entry.sym_type with
        | Some ty -> subst_vars param_subst ty
        | None -> LP.fresh_mvar ()
        end
      | None -> LP.fresh_mvar ()
    in
    { term = term'; ty; constrs }

  (* Pattern variables - look up type from context or assign fresh metavar *)
  | LP.PVar name ->
    let ty = match lookup_local ctx name with
      | Some ty -> ty
      | None -> LP.fresh_mvar ()
    in
    { term = t; ty; constrs = [] }

  (* Metavariables - already have implicit type *)
  | LP.MVar _ -> { term = t; ty = LP.fresh_mvar (); constrs = [] }

  (* Application: f x *)
  | LP.App (f, x) ->
    let res_f = infer ctx f in
    let res_x = infer ctx x in
    (* f should have type (A → B), x should have type A, result is B *)
    let result_ty = LP.fresh_mvar () in
    let expected_f_ty = LP.Arrow (res_x.ty, result_ty) in
    let constrs = res_f.constrs @ res_x.constrs @ [(res_f.ty, expected_f_ty)] in
    { term = LP.App (res_f.term, res_x.term); ty = result_ty; constrs }

  (* Arrow type *)
  | LP.Arrow (a, b) ->
    let res_a = infer ctx a in
    let res_b = infer ctx b in
    { term = LP.Arrow (res_a.term, res_b.term);
      ty = LP.Var "TYPE";  (* Arrow types are TYPE *)
      constrs = res_a.constrs @ res_b.constrs }

  (* Binders *)
  | LP.Bind (binder, params, body) ->
    let (params', ctx', constrs_params) = infer_params ctx params in
    let res_body = infer ctx' body in
    { term = LP.Bind (binder, params', res_body.term);
      ty = LP.fresh_mvar ();  (* TODO: compute proper type *)
      constrs = constrs_params @ res_body.constrs }

  (* Let bindings *)
  | LP.Let (x, e, body) ->
    let res_e = infer ctx e in
    let ctx' = extend_local ctx x res_e.ty in
    let res_body = infer ctx' body in
    { term = LP.Let (x, res_e.term, res_body.term);
      ty = res_body.ty;
      constrs = res_e.constrs @ res_body.constrs }

and infer_params (ctx : context) (params : LP.param list)
    : LP.param list * context * constraints =
  L.fold_left (fun (acc_params, ctx, acc_cs) (name, ty, attr) ->
    let res = infer ctx ty in
    let ctx' = extend_local ctx name res.ty in
    (acc_params @ [(name, res.term, attr)], ctx', acc_cs @ res.constrs)
  ) ([], ctx, []) params

(* ============================================================
   Unification
   ============================================================ *)

let rec unify (subst : LP.meta_subst) (constraints : constraints) : LP.meta_subst option =
  match constraints with
  | [] -> Some subst
  | (t1, t2) :: rest ->
    let t1' = LP.subst_meta subst t1 in
    let t2' = LP.subst_meta subst t2 in
    if t1' = t2' then
      unify subst rest
    else
      match t1', t2' with
      (* Metavariable on left *)
      | LP.MVar n, t ->
        if LP.occurs n t then None
        else unify ((n, t) :: subst) rest

      (* Metavariable on right *)
      | t, LP.MVar n ->
        if LP.occurs n t then None
        else unify ((n, t) :: subst) rest

      (* Structural cases *)
      | LP.App (f1, x1), LP.App (f2, x2) ->
        unify subst ((f1, f2) :: (x1, x2) :: rest)

      | LP.Arrow (a1, b1), LP.Arrow (a2, b2) ->
        unify subst ((a1, a2) :: (b1, b2) :: rest)

      | LP.Const (n1, as1), LP.Const (n2, as2)
        when n1 = n2 && L.length as1 = L.length as2 ->
        let arg_cs = L.map2 (fun (_, a1) (_, a2) -> (a1, a2)) as1 as2 in
        unify subst (arg_cs @ rest)

      | LP.Var v1, LP.Var v2 when v1 = v2 -> unify subst rest
      | LP.PVar v1, LP.PVar v2 when v1 = v2 -> unify subst rest
      | LP.Lit l1, LP.Lit l2 when l1 = l2 -> unify subst rest

      | LP.Bind (b1, ps1, body1), LP.Bind (b2, ps2, body2)
        when b1 = b2 && L.length ps1 = L.length ps2 ->
        let param_cs = L.map2 (fun (_, ty1, _) (_, ty2, _) -> (ty1, ty2)) ps1 ps2 in
        unify subst (param_cs @ [(body1, body2)] @ rest)

      | LP.Let (_, e1, b1), LP.Let (_, e2, b2) ->
        unify subst ((e1, e2) :: (b1, b2) :: rest)

      (* Unification failure - but don't fail, just skip this constraint *)
      | _ -> unify subst rest

(* Normalize substitution: when ?n -> ?m, find canonical representative.
   This ensures that two metavars unified together use the same pattern var. *)
let normalize_subst (subst : LP.meta_subst) : LP.meta_subst =
  (* Find canonical representative for a metavar *)
  let rec find_repr n =
    match L.assoc_opt n subst with
    | Some (LP.MVar m) -> find_repr m
    | Some t -> Some t
    | None -> None
  in
  (* Build normalized substitution *)
  L.filter_map (fun (n, t) ->
    match find_repr n with
    | Some t' -> Some (n, t')
    | None ->
      (* n maps to a chain of metavars ending in unsolved one - find the end *)
      let rec find_end = function
        | LP.MVar m ->
          (match L.assoc_opt m subst with
           | Some (LP.MVar k) -> find_end (LP.MVar k)
           | _ -> LP.MVar m)  (* m is the end of the chain *)
        | t -> t
      in
      Some (n, find_end t)
  ) subst

(* ============================================================
   Main Resolution Entry Points
   ============================================================ *)

(* Resolve a term: infer types, solve constraints, substitute back *)
let resolve (ctx : context) (t : LP.term) : LP.term =
  LP.reset_mvar_counter ();
  let res = infer ctx t in
  match unify [] res.constrs with
  | Some subst -> LP.metas_to_wildcards (LP.subst_meta subst res.term)
  | None -> LP.metas_to_wildcards res.term

let debug_resolve = ref false

(* Resolve a case (LHS, RHS pair) with local type bindings for pattern variables.
   pvar_names: names that should become pattern variables in the result *)
let resolve_case_with_locals (ctx : context) (locals : (string * LP.term) list) ((lhs, rhs) : LP.case) : LP.case =
  LP.reset_mvar_counter ();
  (* Add local type bindings to context *)
  let ctx' = L.fold_left (fun c (name, ty) -> extend_local c name ty) ctx locals in
  (* Extract the names that should become pattern variables *)
  let pvar_names = L.map fst locals in
  let res_lhs = infer ctx' lhs in
  let res_rhs = infer ctx' rhs in
  (* The LHS and RHS should have compatible types (type preservation) *)
  let type_constraint = (res_lhs.ty, res_rhs.ty) in
  let constraints = res_lhs.constrs @ res_rhs.constrs @ [type_constraint] in
  if !debug_resolve then begin
    Printf.eprintf "=== resolve_case ===\n";
    Printf.eprintf "LHS: %s\n" (LP.term_str res_lhs.term);
    Printf.eprintf "LHS type: %s\n" (LP.term_str res_lhs.ty);
    Printf.eprintf "RHS: %s\n" (LP.term_str res_rhs.term);
    Printf.eprintf "RHS type: %s\n" (LP.term_str res_rhs.ty);
    Printf.eprintf "Constraints (%d):\n" (L.length constraints);
    L.iter (fun (t1, t2) -> Printf.eprintf "  %s = %s\n" (LP.term_str t1) (LP.term_str t2)) constraints
  end;
  match unify [] constraints with
  | Some subst ->
    (* Normalize substitution so that metavar chains have canonical representatives *)
    let subst' = normalize_subst subst in
    if !debug_resolve then begin
      Printf.eprintf "Unification succeeded:\n";
      L.iter (fun (n, t) -> Printf.eprintf "  ?%d -> %s\n" n (LP.term_str t)) subst';
    end;
    (* LHS: unsolved metas become pattern variables for type tracking.
       Also convert specified variables to pattern variables. *)
    let lhs' = LP.subst_meta subst' res_lhs.term in
    let lhs'' = LP.metas_to_pvars lhs' in
    let lhs''' = LP.vars_to_pvars pvar_names lhs'' in
    (* RHS: unsolved metas become wildcards for inference.
       Also convert variables to pattern variables (to reference LHS bindings). *)
    let rhs' = LP.subst_meta subst' res_rhs.term in
    let rhs'' = LP.metas_to_wildcards rhs' in
    let rhs''' = LP.vars_to_pvars pvar_names rhs'' in
    (lhs''', rhs''')
  | None ->
    if !debug_resolve then Printf.eprintf "Unification failed\n";
    let lhs' = LP.metas_to_pvars res_lhs.term in
    let lhs'' = LP.vars_to_pvars pvar_names lhs' in
    let rhs' = LP.metas_to_wildcards res_rhs.term in
    let rhs'' = LP.vars_to_pvars pvar_names rhs' in
    (lhs'', rhs'')

(* Resolve a case without extra locals (backwards compatibility) *)
let resolve_case (ctx : context) (case : LP.case) : LP.case =
  resolve_case_with_locals ctx [] case

(* ============================================================
   Context Initialization
   ============================================================ *)

(* Create a fresh context with Prelude builtins *)
let init_context () : context =
  let ctx = create_context () in
  add_prelude_builtins ctx;
  ctx

(* ============================================================
   Debugging
   ============================================================ *)

let constraint_str ((t1, t2) : constraint_) : string =
  LP.term_str t1 ^ " ≈ " ^ LP.term_str t2

let constraints_str (cs : constraints) : string =
  String.concat "\n" (L.map constraint_str cs)

let subst_str (s : LP.meta_subst) : string =
  String.concat "\n" (L.map (fun (n, t) ->
    "?" ^ string_of_int n ^ " ↦ " ^ LP.term_str t
  ) s)
