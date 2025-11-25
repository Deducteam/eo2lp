open Syntax_eo

module M = Map.Make(String)
type 'a pmap = (params * 'a) M.t

(* ---- local context ---- *)
type context =
  {
    typs : term M.t;
    atts : attr M.t;
  }

let is_list (ctx : context) (s : string) : bool =
  match M.find_opt s ctx.atts with
  | Some (Attr ("list", None)) -> true
  | None -> false

let is_implicit (ctx : context) (s : string) : bool =
  match M.find_opt s ctx.atts with
  | Some (Attr ("implicit", None)) -> true
  | None -> false

(* ---- global signature ---- *)
type signature =
  {
    mutable atts : (params * attr) M.t;
    mutable typs : (params * term) M.t;
    mutable defs : (params * term) M.t;
    mutable prgs : (params * cases) M.t;
  }
