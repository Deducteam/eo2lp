open Syntax_eo

module M = Map.Make(String)
type 'a pmap = (params * 'a) M.t

(* ---- DELETEME ---- *)
type context =
  {
    typs : term M.t;
    atts : (attr list) M.t;
  }

let empty_ctx : context =
  { typs = M.empty; atts = M.empty }

let mk_context (ps : param list) : context =
  let f (Param (s, t, xs)) = ((s,t), (s,xs)) in
  let (xs, ys) = List.split (List.map f ps) in
  { typs = M.of_list xs; atts = M.of_list ys }
(* ---------------------------------------------- *)

let find_typ (s : string) (ps : params) : term option =
  let f (Param (s',t,_)) =
    if s = s' then Some t else None
  in
    List.find_map f ps

let find_atts (s : string) (ps : params) : attr list =
  let f (Param (s',_,xs)) =
    if s = s' then Some xs else None
  in
  match List.find_map f ps with
  | Some xs -> xs
  | None -> []

let is_list (ps : params) (s : string) : bool =
  List.mem (Attr ("list", None)) (find_atts s ps)

let is_implicit (ps : params) (s : string) : bool =
  List.mem (Attr ("implicit", None)) (find_atts s ps)

(* ---- global signature ---- *)
type signature =
  {
    mutable atts : (params * attr) M.t;
    mutable typs : (params * term) M.t;
    mutable defs : (params * term) M.t;
    (* mutable prgs : (params * cases) M.t; *)
  }

let is_macro (sgn : signature) (s : string) =
  M.mem s sgn.defs
