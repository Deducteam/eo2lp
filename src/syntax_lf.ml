module L = List
module S = String
module EO = Syntax_eo
module LP = Syntax_lp

open Literal

type term =
  | Con of string * term list
  | Var of string
  | Lit of literal
  | App of term * term
  | Arr of term * term
  | Let of string * term * term

type attr = Implicit | Explicit
type param = string * term * attr
type case = term * term
type symbol =
  | Decl of param list * term
  | Prog of (param list * term) * (param list * case list)
type signature =
  (string * symbol) list



let rec term_str : term -> string =
  function
  | Con (s,[]) | Var s -> s
  | Con (s,ts) ->
    Printf.sprintf "%s[%s]"
      s (ts |> L.map term_str |> S.concat " ")
  | Lit l -> literal_str l
  | Arr (t,t') ->
    Printf.sprintf "%s -> %s"
      (term_str t) (term_str t')
  | App (t,t') ->
    Printf.sprintf "(%s %s)"
      (term_str t) (term_str t')
  | Let (s,t,t') ->
    Printf.sprintf "(let %s := %s in %s)"
      s (term_str t) (term_str t')

let param_str : param -> string =
  function
  | (s,t,Implicit) ->
    Printf.sprintf "[%s : %s]"
      s (term_str t)
  | (s,t,Explicit) ->
    Printf.sprintf "(%s : %s)"
      s (term_str t)

let symbol_str : string * symbol -> string =
  function
  | (s, Decl ([],t)) ->
    Printf.sprintf "%s : %s" s (term_str t)
  | (s, Decl (ps,t)) ->
    Printf.sprintf "%s %s : %s" s
      (S.concat " " (L.map param_str ps))
      (term_str t)
  | (s, Prog ((ps,t), (qs,cs))) ->
    Printf.sprintf "%s %s := cases(...)"
    s (S.concat " " (L.map param_str ps))

(* let rec subst : term -> string -> term -> term =
  fun t x y ->
    match t with
    | Con (s,ts) ->
        Con (s, L.map (fun t -> subst t x y) ts)
    | Var s ->
        if s = x then y else t
    | Lit l ->
        Lit l
    | App (t, t') ->
        App (subst t x y, subst t x y)
    | Arr (t,t') ->
        Arr (subst t x y, subst t x y)
    | Let (s,t,t') ->
        if x = s then Printf.printf "WARNING:
          variable capture during substitution on `Let`.";
        Let (s, subst t x y, subst t x y)

let rec splice
  (ps,t,ts : param list * term * term list)
  : (param list * term * term list)
=
  match ps, ts with
  | (([],_)|(_,[])) -> (ps, t, ts)
  | ((_,_,Implicit) :: ps, ts) ->
      splice (ps, t, ts)
  | ((s,_,Explicit) :: ps, t' :: ts) ->
      splice (ps, subst t s t', ts)

let app_binop : term -> term -> term -> term =
  fun f t1 t2 -> App (App (f, t1), t2)

let app_list : term -> term list -> term =
  fun t ts ->
    L.fold_left (fun acc t -> App (acc, t)) t ts *)
