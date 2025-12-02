type binder =
  | Lambda
  | Pi

type term =
  | PVar of string
  | Wrap of term
  | Var of string
  | App of term * term
  | Bind of binder * param list * term
  | Let of (string * term) * term
and param =
  | Implicit of string * term
  | Explicit of string * term

(* type pattern =
  | PVar of string
  | PApp of string * pattern list

type case =
  | Case of (string * pattern list * pattern) *)
type cases = (term * term) list

type modifier =
  | Constant
  | Sequential

type command =
  | Symbol of
      modifier option * string *
      param list * term option * term option
  | Rule of
      cases
  | Require of
      string list

(* ---- pretty printing -------- *)
let binder_str : binder -> string =
  function
  | Lambda -> "λ"
  | Pi     -> "Π"

let is_atom : term -> bool =
  function
  | Var _ -> true
  | PVar _ -> true
  | Wrap _ -> true
  | _ -> false

let is_pi : term -> bool =
  function
  | Bind (Pi, _, _) -> true
  | _ -> false

let in_params (s : string) (ps : param list) : bool =
  List.exists
    (function
      | (Explicit (s',_) | Implicit (s', _))
        when s = s' -> true
      | _ -> false
    ) ps

let rec term_str : term -> string =
  function
  | Wrap t -> Printf.sprintf "[%s]" (term_str t)
  | Var str -> str
  | PVar str -> "$" ^ str
  | App (App (Var "⤳", t1), t2) when is_atom t2 ->
    Printf.sprintf "%s ⤳ %s"
      (term_str t1)
      (term_str t2)
  | App (App (Var "⤳", t1), t2) ->
    Printf.sprintf "%s ⤳ (%s)"
      (term_str t1)
      (term_str t2)
  | App (App (Var "▫", t1), t2) when is_atom t2 ->
    Printf.sprintf "%s ▫ %s"
      (term_str t1)
      (term_str t2)
  | App (App (Var "▫", t1), t2) ->
    Printf.sprintf "%s ▫ (%s)"
      (term_str t1)
      (term_str t2)
  | App (t1,t2) when is_atom t2 ->
    Printf.sprintf "%s %s"
      (term_str t1)
      (term_str t2)
  | App (t1,t2) ->
    Printf.sprintf "%s (%s)"
      (term_str t1)
      (term_str t2)
  | Bind (Pi,[Explicit ("_",t)],t')->
    if is_pi t then
      Printf.sprintf "(%s) → %s"
        (term_str t)
        (term_str t')
    else
      Printf.sprintf "%s → %s"
        (term_str t)
        (term_str t')
  | Bind (b,xs,t)->
    Printf.sprintf "%s %s, %s"
      (binder_str b)
      (param_list_str xs)
      (term_str t)
  | Let ((s,t),t') ->
    Printf.sprintf "let %s ≔ %s in %s"
      s (term_str t) (term_str t')

and param_str : param -> string =
  function
  | Implicit (s,t) ->
    Printf.sprintf "[%s : %s]"
      s (term_str t)
  | Explicit (s,t) ->
    Printf.sprintf "(%s : %s)"
      s (term_str t)

and param_list_str (xs : param list) : string =
  String.concat " " (List.map param_str xs)

(* let rec pattern_str : pattern -> string =
  function
  | PVar str       -> "%" ^ str
  | PApp (str, ps) ->
    let ps_str =
      String.concat " " (List.map pattern_str ps)
    in
      str ^ " " ^ ps_str *)

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
  (*  printing <m>? symbol <s> <p>* : t <:= t'>? *)
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
