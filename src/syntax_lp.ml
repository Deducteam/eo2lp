
type binder =
  | Lambda | Pi
and term =
  | Var of string
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

module L = List
module S = struct
  include String
  let concat_map s f xs = String.concat " " (L.map f xs)
end

let is_var : term -> bool =
  function
  | Var _ -> true
  | _     -> false

let is_forbidden (s : string) : bool =
  (
    String.contains s '$'
  ||
    String.contains s '@'
  ||
    String.contains s ':'
  ||
    String.contains s '.'
  )

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
  L.map (fun (t,t') -> (f t, f t'))


let app_list : term -> term list -> term =
  L.fold_left (fun acc t -> App (acc, t))


(* ---- pretty printing -------- *)
let binder_str : binder -> string =
  function
  | Lambda -> "λ"
  | Pi     -> "Π"

let rec term_str : term -> string =
  function
  | Var s -> s
  | App (t,t') ->
    Printf.sprintf "(%s %s)"
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

let lp_command_str =
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
