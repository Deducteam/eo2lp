open Literal

module L = List
module S = struct
  include String
  let concat_map s f xs = String.concat " " (L.map f xs)
end

let is_forbidden (s : string) : bool =
  String.contains s '$'
  || String.contains s '@'
  || String.contains s ':'
  || String.contains s '.'

let strip_prefix (str : string) (pre : string) : string =
  let n = String.length pre in
  let m = String.length str in
  (String.sub str n (m - n))

let replace (c, s : char * string) (str : string) : string =
  let xs = String.split_on_char c str in
  String.concat s xs

type binder =
  | Lambda | Pi
and term =
  | Var of string | PVar of string | Lit of literal
  | App of term * term
  | Bind of binder * param list * term
  | Arrow of term * term
  | Let of string * term * term
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

type signature = command list

module EO = Syntax_eo

let app_list : term -> term list -> term =
  fun t ts -> L.fold_left (fun acc t -> App (acc, t)) t ts

(* given `ts = [t1 ... tn], return `t1 ⤳ ... ⤳ tn` *)
let rec arr_list : term list -> term =
  function
  | [] -> failwith "Cannot built arrow type from empty list."
  | t::[] -> t
  | t::ts -> App (App (Var "⤳", t), arr_list ts)

let is_var : term -> bool =
  function
  | Var _ -> true
  | _     -> false
let is_pi : term -> bool =
  function
  | Bind (Pi, _, _) -> true
  | _ -> false

let in_params (s : string) (ps : param list) : bool =
  List.exists (fun (s',_,_) -> s = s') ps

let map_param (f : term -> term) : param -> param =
  function (s,t,att) -> (s,f t,att)

let rec map_vars (f : string -> term) : term -> term =
  function
  | Var s -> f s
  | App (t,t') ->
      App (map_vars f t, map_vars f t')
  | Arrow (t,t') ->
      Arrow (map_vars f t, map_vars f t')
  | Let (s,t,t') ->
      Let (s, map_vars f t, map_vars f t')
  | Bind (b,ps,t) ->
      Bind (b,
        L.map (map_param @@ map_vars f) ps,
        map_vars f t
      )

let map_cases (f : term -> term) : case list -> case list =
  L.map (fun (t,t') -> f t, f t')

let bind_pvars (ps : EO.param list) (t : term)  : term =
  let f s =
    if L.exists (fun (s',_,_) -> s = s') ps
    then PVar s else Var s
  in
    map_vars f t

let tau_of (t : term) =
  App (Var "τ", t)

(* ---- pretty printing -------- *)
let binder_str : binder -> string =
  function
  | Lambda -> "λ"
  | Pi     -> "Π"

let rec term_str : term -> string =
  function
  | Var s -> s
  | Lit l -> literal_str l
  | PVar s -> "$" ^ s
  | App (Var "τ", Var "eo⋅⋅Type") -> "Set"
  | App (App (Var "⤳",t),t') when is_var t ->
    Printf.sprintf "%s ⤳ %s"
      (term_str t) (term_str t')
  | App (App (Var "⤳",t),t') ->
    Printf.sprintf "(%s) ⤳ %s"
      (term_str t) (term_str t')
  | App (t,t') when is_var t' ->
    Printf.sprintf "%s %s"
      (term_str t) (term_str t')
  | App (t,t') ->
    Printf.sprintf "%s (%s)"
      (term_str t) (term_str t')
  | Arrow (t, t') ->
    Printf.sprintf "(%s → %s)"
      (term_str t) (term_str t')
  | Bind (b,xs,t)->
    Printf.sprintf "(%s %s, %s)"
      (binder_str b)
      (S.concat_map " " param_str xs)
      (term_str t)
  | Let (s,t,t') ->
    Printf.sprintf "(let %s ≔ %s in %s)"
      s (term_str t) (term_str t')
and param_str : param -> string =
  function
  | (s,t,Implicit) ->
    Printf.sprintf "[%s : %s]"
      s (term_str t)
  | (s,t,Explicit) ->
    Printf.sprintf "(%s : %s)"
      s (term_str t)

let case_str : (term * term) -> string =
  fun (t,t') ->
    Printf.sprintf "%s ↪ %s"
    (term_str t) (term_str t')

let modifier_str =
  function
  | Constant   -> "constant"
  | Sequential -> "sequential"

let command_str =
  function
  | Symbol (m_opt, str, xs, ty_opt, def_opt) ->
    let m_str = match m_opt with
      | None -> ""
      | Some m -> modifier_str m ^ " "
    in
    let xs_str = match xs with
      | [] -> ""
      | xs -> S.concat_map " " param_str xs
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
      S.concat_map "\nwith " case_str cs
      |> Printf.sprintf "rule %s;"
  (* printing `require open <path>+`  *)
  | Require ps ->
    let ps_str = String.concat " " ps in
    Printf.sprintf "require open %s;" ps_str

let sig_str : signature -> string =
  S.concat_map "\n" command_str
