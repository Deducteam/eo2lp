
type binder =
  | Lambda
  | Pi

type leaf =
  | Type | Set
  | PVar of string
  | Const of string
  | Var of string
and term =
  | Leaf of leaf
  | App of level * term * term
  | Wrap of term
  | El of term
  | Arrow of level * (term list)
  | Bind of binder * param list * term
  | Let of string * term * term
and level = O | M
and attr = Explicit | Implicit
and param = string * term * attr


type case = (term * term)

type modifier =
  | Constant
  | Sequential

type command =
  | Symbol of
      modifier option * string *
      param list * term option * term option
  | Rule of
      case list
  | Require of
      string list

(* ---- pretty printing -------- *)
let binder_str : binder -> string =
  function
  | Lambda -> "λ"
  | Pi     -> "Π"

let is_leaf_or_wrap : term -> bool =
  function
  | Leaf _ -> true
  | Wrap _ -> true
  | _      -> false

let is_pi : term -> bool =
  function
  | Bind (Pi, _, _) -> true
  | _ -> false

let in_params (s : string) (ps : param list) : bool =
  List.exists (fun (s',_,_) -> s = s') ps

let map_param (f : term -> term) : param -> param =
  function (s,t,att) -> (s,f t,att)

let rec map_leaves (f : leaf -> term) : term -> term =
  function
  | Leaf l -> f l
  | Wrap t -> Wrap (map_leaves f t)
  | El t -> El (map_leaves f t)
  | App (lv,t,t') ->
    App (lv, map_leaves f t, map_leaves f t')
  | Arrow (lv,ts) ->
    Arrow (lv, List.map (map_leaves f) ts)
  | Let (s,t,t') ->
    Let (s,map_leaves f t, map_leaves f t')
  | Bind (b,ps,t) ->
    Bind (b,
      List.map (map_param (map_leaves f)) ps,
      map_leaves f t
    )

let map_cases (f : term -> term) (cs : case list) : case list =
  let g (t,t') = (f t, f t') in
  List.map g cs

let rec leaf_str : leaf -> string =
  function
  | Type -> "TYPE"
  | Set -> "Set"
  | PVar s -> "$" ^ s
  | Const s -> s
  | Var s -> s
and term_str : term -> string =
  function
  | Leaf l -> leaf_str l
  | Arrow (lv, ts) ->
    let strs = List.map
      (fun t ->
        if is_leaf_or_wrap t then term_str t
        else "(" ^ term_str t ^ ")"
      ) ts
    in
      String.concat
        (if lv = O then " ⤳ " else " → ") strs
  | El t ->
    Printf.sprintf
      (if is_leaf_or_wrap t then "τ %s" else "τ (%s)")
      (term_str t)
  | Wrap t ->
    Printf.sprintf
      "[%s]"
      (term_str t)
  | App (lv,t,t') ->
    Printf.sprintf
      (if is_leaf_or_wrap t' then "%s%s%s" else "%s%s(%s)")
      (term_str t)
      (if lv = O then " ▫ " else " ")
      (term_str t')
  | Bind (b,xs,t)->
    Printf.sprintf "%s %s, %s"
      (binder_str b)
      (param_list_str xs)
      (term_str t)
  | Let (s,t,t') ->
    Printf.sprintf "let %s ≔ %s in %s"
      s (term_str t) (term_str t')
and param_str : param -> string =
  function
  | (s,t,Implicit) ->
    Printf.sprintf "[%s : %s]"
      s (term_str t)
  | (s,t,Explicit) ->
    Printf.sprintf "(%s : %s)"
      s (term_str t)

and param_list_str (xs : param list) : string =
  String.concat " " (List.map param_str xs)

let case_str : (term * term) -> string =
  function
  | (lhs,rhs) ->
    Printf.sprintf "%s ↪ %s"
      (term_str lhs)
      (term_str rhs)

let modifier_str =
  function
  | Constant   -> "constant"
  | Sequential -> "sequential"

let lp_command_str =
  function
  | Symbol (m_opt, str, xs, ty_opt, def_opt) ->
    let m_str = match m_opt with
      | None -> ""
      | Some m -> modifier_str m ^ " "
    in
    let xs_str = match xs with
      | [] -> ""
      | xs -> param_list_str xs ^ " "
    in
    let ty_str = match ty_opt with
      | None -> ""
      | Some ty -> ": " ^ (term_str ty)
    in
    let def_str = match def_opt with
      | None -> ""
      | Some def -> "≔ " ^ (term_str def)
    in
    Printf.sprintf "%ssymbol %s %s%s%s;"
      m_str str xs_str ty_str def_str
  (* printing `rule <r> <with r>*`  *)
  | Rule cs ->
    let cs_str =
      String.concat "\nwith "
        (List.map case_str cs)
    in
      Printf.sprintf "rule %s;" cs_str
  (* printing `require open <path>+`  *)
  | Require ps ->
    let ps_str = String.concat " " ps in
    Printf.sprintf "require open %s;" ps_str
