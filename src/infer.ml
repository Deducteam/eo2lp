(* Type inference for Eunoia terms during encoding.

   When encoding program patterns, we need to track types for HO applications
   so we can emit explicit type parameters: (⋅ [A] [B] f x) instead of (f ⋅ x).

   This module provides:
   1. Type representation with metavariables
   2. Constraint-based type inference
   3. Unification to solve constraints
   4. Type-annotated term encoding
*)

module EO = Syntax_eo

(* Type metavariables for inference *)
type mvar = int

(* Types during inference - can contain metavariables *)
type ty =
  | TVar of string        (* Type variable from params, e.g., U *)
  | TCon of string        (* Concrete type, e.g., Bool, Int *)
  | TApp of string * ty list  (* Type application, e.g., Seq U, BitVec n *)
  | TArrow of ty * ty     (* Function type: A → B *)
  | TMeta of mvar         (* Metavariable for inference *)

(* Equality constraints *)
type constraint_ = ty * ty

(* Substitution: maps metavariables to types *)
type subst = (mvar * ty) list

(* Fresh metavariable counter *)
let mvar_counter = ref 0
let fresh_mvar () =
  let n = !mvar_counter in
  mvar_counter := n + 1;
  TMeta n

let reset_mvar_counter () =
  mvar_counter := 0

(* Convert Eunoia type term to our ty representation.
   We keep the original Eunoia names (with @ or eo:: prefixes) so eo_name can handle them. *)
let rec ty_of_eo_term (t : EO.term) : ty =
  match t with
  | EO.Symbol "Type" -> TCon "Type"
  | EO.Symbol "Bool" -> TCon "Bool"
  | EO.Symbol "Int" -> TCon "Int"
  | EO.Symbol "Real" -> TCon "Real"
  | EO.Symbol "String" -> TCon "String"
  (* Keep @-prefixed and eo::-prefixed names as TCon (these are concrete types) *)
  | EO.Symbol s when String.length s > 0 && s.[0] = '@' -> TCon s
  | EO.Symbol s when String.length s > 4 && String.sub s 0 4 = "eo::" -> TCon s
  | EO.Symbol s -> TVar s  (* Assume it's a type variable *)
  | EO.Apply ("->", ts) ->
    (* Arrow type: (-> A B C) means A → B → C *)
    begin match ts with
    | [] -> TCon "Unit"
    | [t] -> ty_of_eo_term t
    | t :: rest -> TArrow (ty_of_eo_term t, ty_of_eo_term (EO.Apply ("->", rest)))
    end
  | EO.Apply (tycon, args) ->
    TApp (tycon, List.map ty_of_eo_term args)
  | _ -> TCon "?"  (* Unknown *)

(* Convert ty back to Eunoia term for encoding *)
let rec eo_term_of_ty (t : ty) : EO.term =
  match t with
  | TVar s -> EO.Symbol s
  | TCon s -> EO.Symbol s
  | TApp (c, args) -> EO.Apply (c, List.map eo_term_of_ty args)
  | TArrow (a, b) -> EO.Apply ("->", [eo_term_of_ty a; eo_term_of_ty b])
  | TMeta n -> EO.Symbol (Printf.sprintf "?%d" n)

(* Apply substitution to a type *)
let rec apply_subst (s : subst) (t : ty) : ty =
  match t with
  | TMeta n ->
    begin match List.assoc_opt n s with
    | Some t' -> apply_subst s t'
    | None -> t
    end
  | TArrow (a, b) -> TArrow (apply_subst s a, apply_subst s b)
  | TApp (c, args) -> TApp (c, List.map (apply_subst s) args)
  | _ -> t

(* Occurs check: does metavariable n occur in type t? *)
let rec occurs (n : mvar) (t : ty) : bool =
  match t with
  | TMeta m -> n = m
  | TArrow (a, b) -> occurs n a || occurs n b
  | TApp (_, args) -> List.exists (occurs n) args
  | _ -> false

(* Type variable substitution: maps type variable names to types *)
type tvar_subst = (string * ty) list

(* Apply type variable substitution *)
let rec apply_tvar_subst (ts : tvar_subst) (t : ty) : ty =
  match t with
  | TVar v ->
    begin match List.assoc_opt v ts with
    | Some t' -> apply_tvar_subst ts t'
    | None -> t
    end
  | TArrow (a, b) -> TArrow (apply_tvar_subst ts a, apply_tvar_subst ts b)
  | TApp (c, args) -> TApp (c, List.map (apply_tvar_subst ts) args)
  | _ -> t

(* Combined substitution for both metavars and type vars *)
type full_subst = subst * tvar_subst

let apply_full_subst ((ms, ts) : full_subst) (t : ty) : ty =
  apply_tvar_subst ts (apply_subst ms t)

(* Unify two types, returning updated substitution or None on failure.
   Handles both metavariables and type variables from params. *)
let rec unify_full ((ms, ts) : full_subst) (constraints : constraint_ list) : full_subst option =
  match constraints with
  | [] -> Some (ms, ts)
  | (t1, t2) :: rest ->
    let t1' = apply_full_subst (ms, ts) t1 in
    let t2' = apply_full_subst (ms, ts) t2 in
    if t1' = t2' then
      unify_full (ms, ts) rest
    else
      match t1', t2' with
      | TMeta n, t | t, TMeta n ->
        if occurs n t then None  (* Occurs check failure *)
        else unify_full ((n, t) :: ms, ts) rest
      | TVar v, t | t, TVar v ->
        (* Unify type variable with another type *)
        unify_full (ms, (v, t) :: ts) rest
      | TArrow (a1, b1), TArrow (a2, b2) ->
        unify_full (ms, ts) ((a1, a2) :: (b1, b2) :: rest)
      | TApp (c1, args1), TApp (c2, args2) when c1 = c2 && List.length args1 = List.length args2 ->
        unify_full (ms, ts) (List.combine args1 args2 @ rest)
      | TCon c1, TCon c2 when c1 = c2 -> unify_full (ms, ts) rest
      | _ -> None  (* Unification failure *)

(* Wrapper that uses the old signature for compatibility *)
let rec unify (s : subst) (constraints : constraint_ list) : subst option =
  match unify_full (s, []) constraints with
  | Some (ms, _) -> Some ms
  | None -> None

(* Type context: maps variable names to their types *)
type ctx = (string * ty) list

(* Build context from Eunoia params *)
let ctx_of_params (ps : EO.param list) : ctx =
  List.map (fun (name, ty, _) -> (name, ty_of_eo_term ty)) ps

(* Typed term: Eunoia term annotated with inferred types at each HO application *)
type typed_term =
  | TSymbol of string * ty
  | TLiteral of Literal.literal * ty
  | TApp of string * typed_term list * ty  (* Regular application *)
  | THOApp of typed_term * typed_term * ty * ty  (* HO app: f, x, arg_ty, result_ty *)
  | TBind of string * (string * typed_term) list * typed_term * ty

(* Built-in symbols with known types *)
let builtin_type (s : string) : ty option =
  match s with
  | "true" | "false" -> Some (TCon "Bool")
  | "Type" -> Some (TCon "Type")
  | _ -> None

(* Infer type of term and build typed representation *)
let rec infer_typed (ctx : ctx) (sgn : EO.signature) (t : EO.term)
    : typed_term * ty * constraint_ list =
  match t with
  | EO.Symbol s ->
    let ty = match List.assoc_opt s ctx with
      | Some ty -> ty
      | None ->
        (* Check built-in types first *)
        begin match builtin_type s with
        | Some ty -> ty
        | None ->
          (* Look up in signature *)
          begin match List.assoc_opt s sgn with
          | Some (EO.Decl (ps, ty, _)) ->
            (* Instantiate with fresh metavars for type params *)
            let type_params = List.filter (fun (_, t, _) -> t = EO.Symbol "Type") ps in
            let subst = List.map (fun (name, _, _) -> (name, fresh_mvar ())) type_params in
            let ty' = ty_of_eo_term ty in
            (* Apply substitution for type params *)
            List.fold_left (fun acc (name, mv) ->
              match acc with
              | TVar v when v = name -> mv
              | TArrow (a, b) -> TArrow (
                  (if a = TVar name then mv else a),
                  (if b = TVar name then mv else b))
              | _ -> acc
            ) ty' subst
          | Some (EO.Prog (ps, ty, _)) ->
            ty_of_eo_term ty
          | _ -> fresh_mvar ()
          end
        end
    in
    (TSymbol (s, ty), ty, [])

  | EO.Literal l ->
    let ty = TCon "Literal" in
    (TLiteral (l, ty), ty, [])

  | EO.Apply ("_", [f; x]) ->
    (* HO application: f x where f : A → B *)
    let (tf, ty_f, cs_f) = infer_typed ctx sgn f in
    let (tx, ty_x, cs_x) = infer_typed ctx sgn x in
    let result_ty = fresh_mvar () in
    let constraint_ = (ty_f, TArrow (ty_x, result_ty)) in
    (THOApp (tf, tx, ty_x, result_ty), result_ty, constraint_ :: cs_f @ cs_x)

  | EO.Apply (s, args) ->
    (* Regular application *)
    let typed_args = List.map (infer_typed ctx sgn) args in
    let args_typed = List.map (fun (t, _, _) -> t) typed_args in
    let args_constraints = List.concat_map (fun (_, _, cs) -> cs) typed_args in
    let result_ty = fresh_mvar () in  (* Would need proper type lookup *)
    (TApp (s, args_typed, result_ty), result_ty, args_constraints)

  | EO.Bind (binder, xs, body) ->
    let xs_typed = List.map (fun (name, def) ->
      let (td, _, _) = infer_typed ctx sgn def in
      (name, td)
    ) xs in
    let (tbody, ty_body, cs_body) = infer_typed ctx sgn body in
    (TBind (binder, xs_typed, tbody, ty_body), ty_body, cs_body)

(* Apply full substitution to typed term *)
let rec apply_full_subst_typed ((ms, ts) : full_subst) (t : typed_term) : typed_term =
  let apply_ty = apply_full_subst (ms, ts) in
  match t with
  | TSymbol (name, ty) -> TSymbol (name, apply_ty ty)
  | TLiteral (l, ty) -> TLiteral (l, apply_ty ty)
  | TApp (name, args, ty) ->
    TApp (name, List.map (apply_full_subst_typed (ms, ts)) args, apply_ty ty)
  | THOApp (f, x, arg_ty, res_ty) ->
    THOApp (apply_full_subst_typed (ms, ts) f, apply_full_subst_typed (ms, ts) x,
            apply_ty arg_ty, apply_ty res_ty)
  | TBind (b, xs, body, ty) ->
    TBind (b, List.map (fun (n, t) -> (n, apply_full_subst_typed (ms, ts) t)) xs,
           apply_full_subst_typed (ms, ts) body, apply_ty ty)

(* Infer and resolve types in a term *)
let infer_and_resolve (ctx : ctx) (sgn : EO.signature) (t : EO.term)
    : typed_term option =
  reset_mvar_counter ();
  let (typed, _, constraints) = infer_typed ctx sgn t in
  match unify_full ([], []) constraints with
  | Some full_subst -> Some (apply_full_subst_typed full_subst typed)
  | None -> None

(* Convert ty back to string for debugging *)
let rec ty_to_string (t : ty) : string =
  match t with
  | TVar s -> s
  | TCon s -> s
  | TApp (c, args) -> Printf.sprintf "(%s %s)" c (String.concat " " (List.map ty_to_string args))
  | TArrow (a, b) -> Printf.sprintf "(%s → %s)" (ty_to_string a) (ty_to_string b)
  | TMeta n -> Printf.sprintf "?%d" n

let rec typed_term_to_string (t : typed_term) : string =
  match t with
  | TSymbol (s, ty) -> Printf.sprintf "%s:%s" s (ty_to_string ty)
  | TLiteral (_, ty) -> Printf.sprintf "lit:%s" (ty_to_string ty)
  | TApp (s, args, ty) ->
    Printf.sprintf "(%s %s):%s" s
      (String.concat " " (List.map typed_term_to_string args))
      (ty_to_string ty)
  | THOApp (f, x, arg_ty, res_ty) ->
    Printf.sprintf "(%s ⋅[%s][%s] %s)"
      (typed_term_to_string f)
      (ty_to_string arg_ty)
      (ty_to_string res_ty)
      (typed_term_to_string x)
  | TBind (b, xs, body, ty) ->
    Printf.sprintf "(%s ... %s):%s" b (typed_term_to_string body) (ty_to_string ty)
