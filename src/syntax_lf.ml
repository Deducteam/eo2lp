module L = List
module S = String
module EO = Syntax_eo
module LP = Syntax_lp

open Literal

type term =
  | Const of string * term list
  | Var of string
  | Lit of literal
  | App of term * term
  | Let of string * term * term

type attr = Implicit | Explicit
type param = string * term * attr
type case = term * term
type symbol =
  | Decl of param list * term
  | Prog of (param list * term) * (param list * case list)
type signature =
  (string * symbol) list


let app_list (ts : term list) : term =
  if ts = [] then
    failwith "Can't apply empty list."
  else
  L.fold_left
    (fun acc t -> App (acc, t))
    (L.hd ts) (L.tl ts)

let rec term_str : term -> string =
  function
  | Const (s,[]) | Var s -> s
  | Const (s,ts) ->
    Printf.sprintf "%s[%s]"
      s (ts |> L.map term_str |> S.concat " ")
  | Lit l -> literal_str l
  | App (t,t') ->
    Printf.sprintf "(%s %s)"
    (term_str t) (term_str t')
  | Let (s,t,t') ->
    Printf.sprintf "(let %s := %s in %s)"
      s (term_str t) (term_str t')
