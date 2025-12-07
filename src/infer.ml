open Elaborate

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

(* for elaboration, we only need to track attributes. *)
(* for type inference, we need to track (post-elaboration) types.*)
type signature =
  {
    mutable prm : (param list) M.t;
    mutable typ : term M.t;
    mutable def : term M.t;
    mutable lit : (EO.lit_category * term) list;
  }

type eq = Eq of term * term

let rec infer_typ
  (sgn, ps as ctx : signature * param list)
  : term -> term * eq list =
  function
  | Literal l ->
  (
    match List.assoc_opt (lcat_of l) sgn.lit with
    | Some ty -> (ty, [])
    | None -> Printf.ksprintf failwith
      "ERROR: literal category %s not associated
       with any type in signature."
       (EO.lit_category_str (lcat_of l))
  )
  | Symbol s ->
  (
    match find_param_typ_opt s ps with
    | Some ty -> (ty, [])
    | None ->
    (
      match M.find_opt s sgn.typ with
      | Some ty -> (ty, [])
      | None -> Printf.ksprintf failwith
        "ERROR: type of %s not given
         by signature or parameters." s
    )
  )
  | (App (t1,t2) | Meta (t1,t2)) ->
    let (ty1, xs) = infer_typ ctx t1 in
    let (ty2, ys) = infer_typ ctx t2 in
    (
    match ty1 with
    | App (App (Symbol "->", u), v) ->
      (v, Eq (u, ty2) :: (List.append xs ys))
    | _ -> Printf.ksprintf failwith
      "ERROR: failed to infer type of application.\n
       The type of %s was %s, and the type of %s was %s\n"
       (term_str t1) (term_str ty1)
       (term_str t2) (term_str ty2)
    )
  | Let (xs, t) ->
  (
    match xs with
    | (s,def) :: ys ->
      let (ty, eqs) = infer_typ ctx def in
      let ps' = (s,ty, Explicit) :: ps in
      let (ty',eqs') =
        infer_typ (sgn, ps') (Let (ys, t)) in
      (ty', List.append eqs eqs')
    | [] -> infer_typ ctx t
  )

(* each parameter must have a unique name.
  but these aren't visible in the term structure.
  so for every symbol, we need to descend and insert
  metavariables for all of the implicit parameters.

  so, it would be nice to change every symbol occurrence
  to have a form (s, ty) where any parameters of `s`
  ocurring in `ty` are transformed to fresh metavars.

  then we don't even need the context for inference
  because we don't need to look up types of symbols,

  but this would maybe yet another datatype for terms....

  unless we bring back Const (s, [...])

*)
let infer
  (sgn,ps as ctx : signature * param list)
  (t : term)
=
