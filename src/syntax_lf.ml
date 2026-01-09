module L = List
module S = String
module EO = Syntax_eo

type literal = EO.literal
type level = EO.level

type leaf =
  | Type | Kind
  | Const of string * int
  | Var of string
  | Literal of literal

type term =
  | Leaf of leaf
  | App of level * term * term
  | Arrow of term * term
  | Let of string * term * term

type case = term * term

let app (lv,f,ts : level * term * term list) =
  L.fold_left (fun acc t -> App (lv,acc,t)) f ts

let leaf_str : leaf -> string =
  function
  | Type -> "TYPE"
  | Kind -> "KIND"
  | Const (s,i) -> s ^ (S.make i '\'')
  | Var s -> s
  | Literal l -> EO.literal_str l

let app_delim_str : level -> string =
  function
    | Tm -> " ⋅ "
    | Ty -> " ∗ "
    | Pg -> " "

let rec term_str : term -> string =
  function
  | Leaf l -> leaf_str l
  | App (lv,t1,t2) ->
    Printf.sprintf "%s%s%s"
      (term_str t1)
      (app_delim_str lv)
      (term_str t2)
  | Arrow (t1,t2) ->
    Printf.sprintf "%s ⇒ %s"
      (term_str t1)
      (term_str t2)
  | Let (s,t,t') ->
    Printf.sprintf "let %s := %s in %s"
      s (term_str t) (term_str t')
