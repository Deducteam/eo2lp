open Syntax_eo

module M = Map.Make(String)

let find_typ (s : string) (ps : param list) : term option =
  let f (s',t,_) =
    if s = s' then Some t else None
  in
    List.find_map f ps

let find_atts (s : string) (ps : param list) : attr list =
  let f (s',_,xs) =
    if s = s' then Some xs else None
  in
  match List.find_map f ps with
  | Some xs -> xs
  | None -> []

let is_list (ps : param list) (s : string) : bool =
  List.mem (Attr ("list", None)) (find_atts s ps)

let is_implicit (ps : param list) (s : string) : bool =
  List.mem (Attr ("implicit", None)) (find_atts s ps)


(* symbol information *)
type signature =
  {
    mutable prm : (param list) M.t;
    mutable att : attr M.t;
    mutable typ : term M.t;
    mutable def : term M.t;
    mutable lit : (lit_category * term) list;
  }

let lcat_of : literal -> lit_category =
  function
  | Numeral _  -> NUM
  | Decimal _  -> DEC
  | Rational _ -> RAT
  | Binary _   -> BIN
  | Hexadecimal _ -> HEX
  | String _      -> STR

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

let rec infer_typ (sgn,ps as ctx : signature * param list) : term -> term =
  function
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
  is_kind (infer_typ (sgn,[]) (Symbol s))
(* let is_macro (sgn : signature) (s : string) =
  M.mem s sgn.defs *)
