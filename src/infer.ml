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

type eq = Eq of term * term

(*
  sgn.typ('=') == (-> U U Bool)
  =(U -> ?1) : (-> ?1 (-> ?1 Bool))
*)
let rec pmap_subst (pm : pmap) =
  function
  | (Literal _|Const _) as t -> t
  | Var s ->
    (
      match M.find_opt s pm with
      | Some t -> t
      | None -> Var s
    )
  | App (t1,t2) -> App (pmap_subst pm t1, pmap_subst pm t2)
  | Meta (t1,t2) -> Meta (pmap_subst pm t1, pmap_subst pm t2)
  | Let (xs,t) ->
    let ys =
      List.map (fun (s,def) -> (s, pmap_subst pm def)) xs
    in
      Let (ys, pmap_subst pm t)

let rec infer_typ
  (sgn, ps as ctx : signature * param list)
  : term -> term * eq list =
  function
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
    begin match find_param_typ_opt s ps with
    | Some ty -> (ty, [])
    | None -> Printf.ksprintf failwith
      "ERROR: type of %s not given by parameter list." s
    end
  (* ------------------------ *)
  | Const (s,pm) ->
  (
    match M.find_opt s sgn with
    | Some (_, Some ty, _) -> (pmap_subst pm ty, [])
    | _ -> Printf.ksprintf failwith
      "ERROR: type of %s not given by signature." s
  )
  (* ------------------------ *)
  | (App (t1,t2) | Meta (t1,t2)) ->
    let (ty1, xs) = infer_typ ctx t1 in
    let (ty2, ys) = infer_typ ctx t2 in
    (
      match ty1 with
      | App (App (Const ("->",_), u), v) ->
        (v, Eq (u, ty2) :: (List.append xs ys))
      | _ -> Printf.ksprintf failwith
        "ERROR: failed to infer type of application.\n
        The type of %s was %s, and the type of %s was %s\n"
        (term_str t1) (term_str ty1)
        (term_str t2) (term_str ty2)
    )
  (* ------------------------ *)
  | Let (xs, t) ->
    begin match xs with
    | (s,def) :: ys ->
      let (ty, eqs) = infer_typ ctx def in
      let ps' = (s,ty, Explicit) :: ps in
      let (ty',eqs') = infer_typ (sgn, ps') (Let (ys, t)) in
      (ty', List.append eqs eqs')
    | [] -> infer_typ ctx t
    end
(* ------------------------ *)

(* let tsig : signature =
  let b = Const ("Bool", M.empty) in
  let i = Const ("Int", M.empty) in
  let typ = Const ("Type", M.empty) in
  let arr x y = App(App(Const ("->", M.empty), x),y) in
  {
  prm = M.of_list [
    ("=", [("U", typ, Implicit)])
  ];
  typ = M.of_list [
    ("Bool", typ);
    ("Int", typ);
    ("0", i);
    ("true", b);
    ("false", b);
    ("or", arr b (arr b b));
    ("=", arr (Var "U") (arr (Var "U") b))
    ];
  def = M.empty;
  lit = [];
} *)
let infer
  (sgn,ps as ctx : signature * param list)
  (t : term)
=
  let (ty, eqs) = infer_typ ctx t in
  ty
