open Syntax_eo
open Interface_eo

let eo_list_concat : term -> (term * term) -> term =
  fun f (t1,t2) ->
    Apply (Symbol "eo::list_concat", [f;t1;t2])

let param_atts : param -> attr list =
  function Param (_,_,atts) -> atts

let list_attr : attr = Attr (Colon "list", None)

let var_has_attr
  (ps : params) (s : symbol) (att : attr) : bool
=
  List.exists
    (fun p -> List.mem att (param_atts p)) ps

(* TODO. how should we account for attributed constants wrt. a list of parameters??? *)
let const_get_attr
  (js : jlist) (s : symbol) : attr option
=
  List.find_map
  (fun j ->
    match j with
    | AttrJ (s', _, att) when s = s' -> Some att
    | _ -> None
  ) js

let const_has_attr
  (js : jlist) (s : symbol) (att : attr) : bool
=
  List.exists (fun j ->
    match j with
    | AttrJ (s, _, att') -> att = att'
    | _ -> false
  ) js


let app ((t1,t2) : term * term) : term =
  Apply (Symbol "_", [t1;t2])

let app_binop (f : term) : term * term -> term =
  fun (t1,t2) -> app (app (f,t1), t2)

let glue (ps : params) (f : term) : (term * term) -> term =
  fun (t1,t2) ->
    match t1 with
    | Sym s when var_has_attr ps s list_attr ->
      eo_list_concat f (t1,t2)
    | _ -> app_binop f (t1,t2)

let rec elab (js : jlist) (ps : params) : term -> term =
  function
  | Sym f -> Sym f
  | Apply (f, ts) ->
    let g  = glue ps (Sym f) in
    let g' = fun (x,y) -> g (y,x) in
    let ts' = List.map (elab js ps) ts in
    match const_get_attr js f with
    | Some (Attr (Colon "right-assoc-nil", Some t_nil)) ->
        failwith ""
    | Some (Attr (Colon "left-assoc-nil", Some t_nil)) ->
        failwith ""
    | Some (Attr (Colon "right-assoc", None)) ->
        failwith ""
    | Some (Attr (Colon "left-assoc", None)) ->
        failwith ""
    | None -> Apply (f, ts')
