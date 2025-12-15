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

(* perform substitution given by a parameter map.*)
let rec pmap_subst (PMap xs as pm : pmap) =
  let f = pmap_subst pm in
  function
  | (Literal _|Const _| MVar _) as t -> t
  | Var s ->
    begin match List.assoc_opt s xs with
      | Some t -> t
      | None -> Var s
    end
  | App (t1,t2)  -> App (f t1, f t2)
  | Meta (t1,t2) -> Meta (f t1, f t2)
  | Let (xs,t) ->
    let ys =
      List.map (fun (s,def) -> (s, f def)) xs
    in
      Let (ys, f t)


(* type of metavariable maps.  *)
type mmap = MMap of ((string * int) * term) list

(* perform substitution given by a metavar map.*)
let rec mmap_subst (MMap xs as mm : mmap) =
  let f = mmap_subst mm in
  function
  | (Literal _|Const _|Var _) as t -> t
  | MVar (s,i) ->
    begin match List.assoc_opt (s,i) xs with
      | Some t -> t
      | None -> Var s
    end
  | App (t1,t2) -> App (f t1, f t2)
  | Meta (t1,t2) -> Meta (f t1, f t2)
  | Let (xs,t) ->
    let ys =
      List.map (fun (s,def) -> (s, f def)) xs
    in
      Let (ys, f t)

(* generate list of metavariable ocurrences in a term. *)
let rec mvars_in : term -> (string * int) list =
  function
  | (Literal _|Const _|Var _) -> []
  | MVar (s,i) -> [(s,i)]
  | App (t1,t2) | Meta (t1,t2) ->
    List.append (mvars_in t1) (mvars_in t2)
  | Let (xs,t) ->
    let mvs =
      List.concat_map (fun (_,def) -> mvars_in def) xs
    in
      List.append mvs (mvars_in t)

(* given some mmap `mm` and maplet `(m ↦ t)`,
  propagate the substitution throughout `mm`. *)
let mmap_update (MMap xs : mmap)
  (mt : (string * int) * term) : mmap
=
  let f ((s,i), t) =
    if List.mem (s,i) (mvars_in t) then
      Printf.ksprintf failwith
        "ERROR: %s occurs in %s"
        (term_str (MVar (s, i))) (term_str t)
    else
      ((s,i), mmap_subst (MMap [mt]) t)
  in
    MMap (mt :: List.map f xs)

(* given some metavar map `mm` and list of equalities `es`,
  apply the metavar substitution to both sides of each
  equality in `es`.*)
let eqs_update (mm : mmap) (es : eq list) : eq list =
  let f (Eq (t,t')) =
    Eq (mmap_subst mm t, mmap_subst mm t')
  in
    List.map f es

(* given a term `t`, signature `sgn` and params `ps`,
   perform type inference to give a term (possibly
   containing metavariables) and eq-constraints.
*)
let rec infer
  (sgn, ps as ctx : EO.signature * EO.param list)
  (qs : param list) (t : term) : term * eq list =
  begin match t with
  (* ------------------------ *)
  | Literal l -> failwith "LITERAL!\n"
    (* match List.assoc_opt (lcat_of l) sgn.lit with
    | Some ty -> (ty, [])
    | None -> Printf.ksprintf failwith
      "ERROR: literal category %s not associated
       with any type in signature."
       (EO.lit_category_str (lcat_of l)) *)
  (* ------------------------ *)
  | Var s ->
    begin match EO.find_param_typ_opt s ps with
    | Some ty -> (desugar ctx ty, [])
    | None -> Printf.ksprintf failwith
      "ERROR: type of %s not given by parameter list." s
    end
  (* ------------------------ *)
  | Const (s,pm) ->
    begin match M.find_opt s sgn with
    | Some info ->
      begin match info.EO.typ with
      | Some ty -> (pmap_subst pm (desugar ctx ty), [])
      | _ -> Printf.ksprintf failwith
        "ERROR: type of %s not given by signature." s
      end
    | _ -> Printf.ksprintf failwith
      "ERROR: symbol %s not registered in signature." s
    end
  (* ------------------------ *)
  | (App (t1,t2) | Meta (t1,t2)) ->
    let (ty1, xs) = infer ctx qs t1 in
    let (ty2, ys) = infer ctx qs t2 in
    begin match ty1 with
    | App (App (Const ("->",_), u), v) ->
      (v, Eq (u, ty2) :: (List.append xs ys))
    | _ -> Printf.ksprintf failwith
      "ERROR: failed to infer type of application.\n
      The type of %s was %s, and the type of %s was %s\n"
      (term_str t1) (term_str ty1)
      (term_str t2) (term_str ty2)
      end
  (* ------------------------ *)
  | Let (xs, t) ->
    (* `infer` needs to take `qs` for post-elaboration
      params to support let properly. *)
    begin match xs with
    | (s,def) :: ys ->
      let (ty, eqs) = infer ctx qs def in
      let qs' = (s,ty,Explicit) :: qs in
      let (ty',eqs') = infer ctx qs' (Let (ys, t)) in
      (ty', List.append eqs eqs')
    | [] -> infer ctx qs t
    end
  end

(* given a metavariable map `mm` (init; MMap []),
  and constraints `es`, calculate the appropriate
  metavariable map by unification.*)
let rec unify (MMap xs as mm : mmap)
  : eq list -> mmap
=
  begin function
  | [] -> mm
  | Eq (t1,t2) :: es ->
    let (t1',t2') =
      (mmap_subst mm t1, mmap_subst mm t1)
    in begin match (t1',t2') with
    (* ---------------- *)
    | (MVar (s,i), MVar (s',j)) when s = s' && i = j ->
      unify mm es
    | (MVar (s,i), _) ->
      let mm' = mmap_update mm ((s,i), t2') in
      let es' = eqs_update mm es in
      unify mm' es'
    | (_, MVar (s,i)) ->
      let mm' = mmap_update mm ((s,i), t1') in
      let es' = eqs_update mm es in
      unify mm' es'
    (* ---------------- *)
    | (App (f, x), App (g,y)) | (Meta (f,x), Meta (g,y)) ->
      unify mm (Eq (f,g) :: Eq (x,y) :: es)
    (* ---------------- *)
    | (Let (xs, t), Let (ys, t')) ->
      begin match (xs,ys) with
      | ([],[]) -> unify mm (Eq (t,t') :: es)
      | ((x,xd)::xs, (y,yd)::ys) ->
        let eq = Eq (Let (xs, t), Let (ys, t')) in
        unify mm (Eq (xd,yd) :: eq :: es)
      end
    (* ---------------- *)
    | ((_ as x), (_ as y)) when x = y ->
      unify mm es
    end
  end

(* given a term `t` and context `sgn,ps`.
   return the resolved form of `t` and its type.    *)
let resolve
  (sgn,ps as ctx : EO.signature * EO.param list)
  (tm : term) : term * term
=
  let (ty, eqs) = infer ctx [] tm in
  let mm = unify (MMap []) eqs in
  (mmap_subst mm tm, mmap_subst mm ty)

(* pretty print an metavariable map. *)
let mmap_str (MMap xs : mmap) : string =
  let f ((s,i),t) =
    (term_str (MVar (s,i))) ^ " ↦ " ^ term_str t
  in
    String.concat ", " (List.map f xs)
