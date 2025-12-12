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

let rec pmap_subst (PMap xs as pm : pmap) =
  let f = pmap_subst pm in
  function
  | (Literal _|Const _| MVar _) as t -> t
  | Var s ->
    begin match List.assoc_opt s xs with
      | Some t -> t
      | None -> Var s
    end
  | App (t1,t2) ->
    App (f t1, f t2)
  | Meta (t1,t2) ->
    Meta (f t1, f t2)
  | Let (xs,t) ->
    let ys =
      List.map (fun (s,def) -> (s, f def)) xs
    in
      Let (ys, f t)

type mmap = MMap of ((string * int) * term) list
let rec mmap_subst (MMap xs as mm : mmap) =
  let f = mmap_subst mm in
  function
  | (Literal _|Const _|Var _) as t -> t
  | MVar (s,i) ->
    begin match List.assoc_opt (s,i) xs with
      | Some t -> t
      | None -> Var s
    end
  | App (t1,t2) ->
    App (f t1, f t2)
  | Meta (t1,t2) ->
    Meta (f t1, f t2)
  | Let (xs,t) ->
    let ys =
      List.map (fun (s,def) -> (s, f def)) xs
    in
      Let (ys, f t)

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

(* given some mmap `xs` and maplet `(m ↦ t)`,
  propogate this substitution throughout `mm`. *)
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

let eqs_update (mm : mmap) (es : eq list) : eq list =
  let f (Eq (t,t')) =
    Eq (mmap_subst mm t, mmap_subst mm t')
  in
    List.map f es

let mmap_str (MMap xs : mmap) : string =
  let f ((s,i),t) =
    (term_str (MVar (s,i))) ^ " ↦ " ^ term_str t
  in
    String.concat ", " (List.map f xs)


let rec infer_typ
  (sgn, ps as ctx : signature * param list)
  : term -> term * eq list =
  begin function
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
  end

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

let infer
  (sgn,ps as ctx : signature * param list)
  (tm : term) : term * term
=
  let (ty, eqs) = infer_typ ctx tm in
  let mm = unify (MMap []) eqs in
  (mmap_subst mm tm, mmap_subst mm ty)

let infer_command
  (sgn : signature) : command -> command
=
  begin function
  | Decl (s,ps,t) ->
    let (t', ty) = infer (sgn,ps) t in
    Decl (s,ps,t')
  (* -------------------- *)
  | Defn (s,ps,t,ty_opt) ->
    let (t', ty) = infer (sgn,ps) t in
    Defn (s,ps,t',ty_opt)
  (* -------------------- *)
  | Prog (s,ps,ty,cs) ->
    let (ty', _) = infer (sgn,ps) ty in
    Prog (s,ps,ty',cs)
  | Rule (s,ps,rd) ->
    Rule (s,ps,rd)
  (* -------------------- *)
  end
