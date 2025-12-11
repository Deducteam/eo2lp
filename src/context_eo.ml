(*
  Code for interacting with Eunoia contexts:
  (i.e., parameter lists, signatures)
*)
open Syntax_eo
module M = Map.Make(String)

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
  let f (s',_,att_opt) =
    if s = s' then att_opt else None
  in
    List.find_map f ps

let is_list_param =
  fun s ps -> (find_param_attr_opt s ps) = (Some List)

let is_implicit_param =
  fun s ps -> (find_param_attr_opt s ps) = (Some Implicit)

let is_opaque_param =
  fun s ps -> (find_param_attr_opt s ps) = (Some Opaque)

(* for elaboration, we only need to track attributes. *)
(* for type inference, we need to track (post-elaboration) types.*)


(*

(*  *)
let rec unsafe_app_ty (t : term) (ts : term list) : term =
  match t with
  | Apply ("->", ts') ->
      if ts' = [] then
        failwith "Too many arguments applied to type!"
      else
        let t' = Apply ("->", ts') in
        unsafe_app_ty t' (List.tl ts)
  | Symbol s ->
      Apply (s, ts)
| _ ->
    failwith "Can't apply this type."

(* the only kind constructors are:
- `Type` (constant)
- `->`   (n-ary) *)
let rec is_kind : term -> bool =
  function
  | Symbol s -> (s = "Type")
  | Apply (s, ts) ->
    if s = "->" then
      is_kind (List.hd (List.rev ts))
    else
      false
  | _ -> false


(*
  really, inference has to happen after elaboration so that
  right-assoc-nil etc are calculated correctly. otherwise
  we have to interleave type inference and elaboration.

  but then it would be better to have binary meta applications...

  okay....

  @@pair : (-> U (-> T (@Pair U T))), prm(@@pair) = {U,T}
  set.empty : U
  true : Bool
  ----------------------------------------
  @@pair true : (-> T (@Pair U T)),
  {U == Bool}

  equality constraints are gathered during inference.
  if needed, we can mark the 'bound parameters' as metavariables.

  when inferring `(s e1 ... en)`, we lookup the type of `s`.
  which will/should be an arrow type (??), e.g.;
    `(-> t1 ... tm)`.
  we (recursively) calculate the types of e1 ... en
  as t'1 ... t'n and zip, which will either be of length n or m.
  call this length l.

  for each pair (ti, t'i), we generate a constraint.

  then, we return the 'candidate type' of our application
*)
let rec infer_typ (sgn,ps as ctx : signature * param list)
  : term -> term = function
  (* ---------------- *)
  | Symbol s ->
    ( (* is `s` locally bound? *)
      match find_typ s ps with
      | Some ty -> ty
      | None ->
      ( (* is `s` in the signature? *)
        match M.find_opt s sgn.typ with
        | Some ty -> ty
        | None -> (* was `s` given by a definition? *)
        (
          match M.find_opt s sgn.def with
          | Some t -> infer_typ ctx t
          | None -> Printf.ksprintf failwith
            "Symbol %s not declared or defined in signature." s
        )
      )
    )
  (* ---------------- *)
  | Literal l ->
    (
      match List.assoc_opt (lcat_of l) sgn.lit with
      | Some ty -> ty
      | None -> Printf.ksprintf failwith
        "Literal category %s not associated with any type."
        (lit_category_str (lcat_of l))
    )
  (* ---------------- *)
  | Apply (s,ts) as t ->
    if s = "->" then
      if is_kind t then Symbol "Kind" else Symbol "Type"
    else
      let s_ty   = infer_typ ctx (Symbol s) in
      let ts_tys = List.map (infer_typ ctx) ts in
      unsafe_app_ty s_ty ts_tys
  (* ---------------- *)
  | Bind (s, xs, t) ->
      failwith "type inference for binder not implemented yet."
  (* ---------------- *)
  | Bang (t,_) -> infer_typ ctx t


let is_tycon (sgn : signature) (s : string) : bool =
  if (s = "->") then true else
  is_kind (infer_typ (sgn,[]) (Symbol s)) *)
