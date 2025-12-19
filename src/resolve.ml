open Desugar

(* elaboration and resolution need to be intertwined.
  if not, we get the following:

declare @@pair⟨[U : Type];[T : Type]⟩
  : (U ~> (T ~> ((@Pair⟨⟩ U) T)))

define @pair⟨⟩ := @@pair⟨U ↦ ?U0, T ↦ ?T0⟩

  i.e., `@pair` doesn't have any parameters according
  to the signature, and so further occurences wont
  be elaborated properly.

  so, when elaborating the raw `define` command for @pair,
  we need to elaborate and resolve the left hand side.
  this reveals that we have 'free parameters' that `@pair`
  must inherit.

  but interestingly, elaboration uses EO.signature,
  but elaboration uses Elab.signature. so we would need to
  update the pre-elaboration signature to register the
  parameters of `@pair`.

  in this case, the parameters of @pair should be U and T.
  but in general, we must use the 'fresh' names generated
  during elaboration to avoid clashes.

  tbh. we should reconsider how we deal with the signature
  anyway.

  so, really. elaboration has two parts:
    desugaring and resolution.
*)

(* ---- some 'duplicate' definitions ----- *)
(* find the type of `s` wrt. `ps`. *)
let find_param_typ_opt
  (s : string) (ps : param list) : term option =
  let f (s',t,_) =
    if s = s' then Some t else None
  in
    List.find_map f ps

(* find the attribute of `s` wrt. `ps`.  *)
let find_param_attr_opt
  (s : string) (ps : param list) : param_attr option =
  let f (s',_,att) =
    if s = s' then Some att else None
  in
    List.find_map f ps

let is_implicit_param s ps =
  (find_param_attr_opt s ps) = (Some Implicit)

let is_opaque_param s ps =
  (find_param_attr_opt s ps) = (Some Opaque)
(* ----------------- *)

(* equations for constraints. *)
type eq = Eq of term * term

let rec map_leaves (f : leaf -> term) : term -> term =
  function
  | Leaf l -> f l
  | App (lv,t,t') ->
    App (lv, map_leaves f t, map_leaves f t')
  | Arrow (lv,ts) ->
    Arrow (lv, List.map (map_leaves f) ts)
  | Let ((s,t), t') ->
    Let ((s, map_leaves f t), map_leaves f t')

let rec pmap_subst (xs : pmap) (t : term) : term =
  let f : leaf -> term =
    function
    | Var s ->
      begin match List.assoc_opt s xs with
      | Some t -> t
      | None -> Leaf (Var s)
      end
    | Type -> Leaf Type
    | Kind -> Leaf Kind
    | Literal l  -> Leaf (Literal l)
    | SVar (s,i) -> Leaf (SVar (s,i))
    | Const (s, ps) ->
      let f' (s,t') = (s, pmap_subst xs t') in
      let ps' = List.map f' ps in
      Leaf (Const (s, ps'))
  in
    map_leaves f t

(* type of schematic variable maps. *)
type svmap = ((string * int) * term) list

(* perform substitution given by a metavar map.*)
let rec svmap_subst (xs : svmap) (t : term) =
  let f : leaf -> term =
    function
    | Type -> Leaf Type
    | Kind -> Leaf Kind
    | Var s -> Leaf (Var s)
    | Literal l  -> Leaf (Literal l)
    | SVar (s,i) -> Leaf (SVar (s,i))
    | Const (s, ps) ->
      let ps' =
        List.map (fun (s,t') -> (s, svmap_subst xs t')) ps
      in
        Leaf (Const (s, ps'))
  in
    map_leaves f t

(* list of schematic variable ocurrences in a term. *)
let rec svars_in : term -> (string * int) list =
  function
  | Leaf (SVar (s,i)) -> [(s,i)]
  | Leaf _ -> []
  | App (lv,t1,t2) ->
    List.append (svars_in t1) (svars_in t2)
  | Arrow (lv,ts) ->
    List.concat_map svars_in ts
  | Let ((s,t),t') ->
    List.append (svars_in t) (svars_in t')

(* given some mmap `mm` and maplet `(m ↦ t)`,
  propagate the substitution throughout `mm`. *)
let svmap_update
  (xs : svmap) (x : (string * int) * term) : svmap
=
  let f (v, t) =
    if List.mem v (svars_in t) then
      Printf.ksprintf failwith
        "ERROR: %s occurs in %s"
        (term_str (Leaf (SVar (fst v, snd v))))
        (term_str t)
    else
      (v, svmap_subst [x] t)
  in
    (x :: List.map f xs)

(* given some metavar map `mm` and list of equalities `es`,
  apply the metavar substitution to both sides of each
  equality in `es`.*)
let eqs_update (xs : svmap) (es : eq list) : eq list =
  let f (Eq (t,t')) =
    Eq (svmap_subst xs t, svmap_subst xs t')
  in
    List.map f es

let type_const = Const ("Type", [])

(* given a term `t`, signature `sgn` and params `ps`,
   perform type inference to give a term (possibly
   containing metavariables) and eq-constraints.
*)
let rec infer
  (sgn,ps as ctx : context)
  (t : term) : term * eq list
=
  begin match t with
  (* ------------------------ *)
  | Leaf (SVar (_,_)) -> failwith
    "ERROR: infer not defined for schematic variables!";
  (* ------------------------ *)
  | Leaf (Literal l) -> failwith
    "ERROR: infer not defined for literals!";
  (* ------------------------ *)
  | Leaf (Var s) ->
    begin match find_param_typ_opt s ps with
    | Some ty -> (ty, [])
    | None -> Printf.ksprintf failwith
      "ERROR: variable `%s` not given by params." s
    end
  (* ------------------------ *)
  | Leaf Type -> (Leaf Kind, [])
  (* ------------------------ *)
  | Leaf Kind -> failwith
    "ERROR: infer not defined for KIND!"
  (* ------------------------ *)
  | Leaf (Const (s,xs)) ->
    begin match M.find_opt s sgn with
    | Some info -> (pmap_subst xs info.typ, [])
    | None -> Printf.ksprintf failwith
      "ERROR: constant `%s` not given by signature." s
    end
  (* ------------------------ *)
  | Arrow (lv,ts) ->
    let es =
      List.concat_map (fun t -> snd (infer ctx t)) ts
    in
      if lv = M then (Leaf Kind, es) else (Leaf Type, es)
  (* ------------------------ *)
  | App (_,t1,t2) ->
    let (ty1, xs) = infer ctx t1 in
    let (ty2, ys) = infer ctx t2 in
    begin match ty1 with
    | (Arrow (lv, t :: ts)) ->
      (
        Arrow (lv, ts),
        Eq (t, ty2) :: (List.append xs ys)
      )
    | _ -> Printf.ksprintf failwith
      "ERROR: failed to infer type of application.\n
      The type of %s was %s, and the type of %s was %s\n"
      (term_str t1) (term_str ty1)
      (term_str t2) (term_str ty2)
    end
  (* ------------------------ *)
  | Let ((s,def), t) ->
    let (def_ty, es) = infer ctx def in
    let ctx' = (sgn, (s,def_ty,Explicit) :: ps) in
    let (t_ty,fs) = infer ctx' t in
    (t_ty, List.append es fs)
  end

(* given a metavariable map `mm` (init; MMap []),
  and constraints `es`, calculate the appropriate
  metavariable map by unification.*)
let rec unify (xs : svmap) : eq list -> svmap =
  begin function
  | [] -> xs
  | Eq (t1,t2) :: es ->
    let (t1',t2') = (svmap_subst xs t1, svmap_subst xs t2) in
    begin match (t1',t2') with
    (* ---------------- *)
    | (Leaf SVar (s,i), Leaf SVar (s',j))
      when s = s' && i = j -> unify xs es
    | (Leaf SVar (s,i), _) ->
      let ys = svmap_update xs ((s,i), t2') in
      let fs = eqs_update xs es in
      unify ys fs
    | (_, Leaf SVar (s,i)) ->
      let ys = svmap_update xs ((s,i), t1') in
      let fs = eqs_update xs es in
      unify ys fs
    (* ---------------- *)
    | (App (lv, f, x), App (lv',g,y)) when lv = lv' ->
      unify xs (Eq (f,g) :: Eq (x,y) :: es)
    (* ---------------- *)
    | (Let ((x,xd), t), Let ((y,yd), t')) ->
      unify xs (Eq (xd,yd) :: Eq (t,t') :: es)
    (* ---------------- *)
    | ((_ as t), (_ as t')) when t = t' ->
      unify xs es
    end
  end

(* pretty print a metavariable map. *)
let svmap_str (xs : svmap) : string =
  let f ((s,i),t) =
    (term_str (Leaf (SVar (s,i)))) ^ " ↦ " ^ term_str t
  in
    String.concat ", " (List.map f xs)

(* pretty print a metavariable map. *)
let eq_list_str (es : eq list) : string =
  let f (Eq (t,t')) =
    (term_str t) ^ " ≡ " ^ (term_str t')
  in
    String.concat ", " (List.map f es)


(* given a term `t` and context `sgn,ps`.
   return the resolved form of `t` and its type.    *)
let resolve
  (sgn,ps as ctx : context)
  (t : term) : term * term
=
  Printf.printf "Begin resolving `%s`\n" (term_str t);
  let (ty, es) = infer ctx t in
    (* Printf.printf
      "Type of `%s` was `%s` with constraints [%s]\n"
      (term_str t) (term_str ty) (eq_list_str es); *)

  let xs = unify [] es in
  (* Printf.printf "Solution found: [%s]\n"
    (svmap_str xs); *)

  let (t',ty') = (svmap_subst xs t, svmap_subst xs ty) in
  Printf.printf "Resolved: `%s` with type `%s`\n"
    (term_str t') (term_str ty');

  (t',ty')

(* let resolve_term ctx trm = fst (resolve ctx ctx' trm) *)
(* let resolve_type ctx trm = snd (resolve ctx ctx' trm) *)
