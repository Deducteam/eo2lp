open Syntax_eo
open Interface_eo

let param_sym : param -> symbol =
  function Param (s,_,_) -> s

let param_atts : param -> attr list =
  function Param (_,_,atts) -> atts

let list_attr : attr     = Attr (Colon "list", None)
let implicit_attr : attr = Attr (Colon "implicit", None)

let var_has_attr
  (ps : params) (s : symbol) (att : attr) : bool
=
  let f (Param (s',_,xs)) = (s = s' && List.mem att xs) in
  List.exists f ps


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

let app_list (f : term) (ts : term list) : term =
  List.fold_left (fun t_acc t -> app (t_acc,t)) f ts

let eo_list_concat_sym : symbol = (Symbol "eo::list_concat")

let eo_list_concat : term -> (term * term) -> term =
  fun f (t1,t2) ->
    app_list (Sym eo_list_concat_sym) [f;t1;t2]

let glue (ps : params) (f : term) : term -> term -> term =
  fun t1 t2 ->
    match t1 with
    | Sym s when var_has_attr ps s list_attr ->
      eo_list_concat f (t1,t2)
    | _ -> app_binop f (t1,t2)

let split_last (xs : 'a list) : ('a list * 'a) =
  let ys = List.rev xs in
  (List.rev (List.tl ys), List.hd ys)

let rec elab (js : jlist) (ps : params) : term -> term =
  function
  | Sym f -> Sym f
  | Bind (s, xs, t) -> failwith ""
  | Apply (f, ts) ->
    let g  = glue ps (Sym f) in
    let g' = fun x y -> g y x in
    let ts' = List.map (elab js ps) ts in
    match const_get_attr js f with
    | Some (Attr (Colon "right-assoc-nil", Some t_nil)) ->
      List.fold_right g ts' t_nil
    | Some (Attr (Colon "left-assoc-nil", Some t_nil)) ->
      List.fold_left g' t_nil ts'
    | Some (Attr (Colon "right-assoc", None)) ->
      let (xs, x) = split_last ts' in
      List.fold_right g xs x
    | Some (Attr (Colon "left-assoc", None)) ->
      (* let (xs, x) = split_last ts' in *)
      List.fold_left g' (List.hd ts') (List.tl ts')
    | None -> app_list (Sym f) ts'

let (test_ps, test_ts) : params * term list =
  let orr = Symbol "or" in
  let bl = Sym (Symbol "Bool") in
  let [x;y;z;w] =
    List.map
      (fun str -> (Symbol str))
      ["x";"y";"z";"w"]
  in
  (
  [
    Param (x, bl, []);
    Param (y, bl, []);
    Param (z, bl, [list_attr]);
    Param (w, bl, [list_attr])
  ]
    ,
  [
    Apply (orr, [Sym x; Sym y]);
    Apply (orr, [Sym x; Sym z]);
    Apply (orr, [Sym x; Sym z;Sym y]);
    Apply (orr, [Sym x]);
    Apply (orr, [Sym z]);
    Apply (orr, [Sym z; Sym y; Sym w; Sym x]);
  ]
  )

let test_or_elab : jlist -> string list =
  fun js ->
    (List.map (fun t -> term_str (elab js test_ps t)) test_ts)
(*
      eo::list : (a -> a -> a) -> a list -> a  *)
