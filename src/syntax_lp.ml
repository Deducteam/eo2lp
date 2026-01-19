open Literal

module L = List
module S = struct
  include String
  let concat_map s f xs = String.concat s (L.map f xs)
end

(* LambdaPi reserved keywords that must be escaped *)
let reserved_keywords = [
  "as"; "in"; "let"; "open"; "require"; "rule"; "symbol"; "with";
  "assert"; "assertnot"; "builtin"; "compute"; "constant"; "debug";
  "definition"; "flag"; "injective"; "opaque"; "prefix"; "print";
  "private"; "protected"; "prover"; "prover_timeout"; "proofterm";
  "quantifier"; "sequential"; "type"; "TYPE"; "unif_rule"; "verbose";
  "why3"; "begin"; "end"; "inductive"; "notation"; "infix"; "postfix";
  "λ"; "Π"; "→"; "↪"; "≔"; "∀"; "∃"; "τ"; "π";
]

let is_reserved (s : string) : bool =
  List.mem s reserved_keywords

let is_forbidden (s : string) : bool =
  String.contains s '$'
  || String.contains s '@'
  || String.contains s ':'
  || String.contains s '.'
  || is_reserved s

let strip_prefix (pre : string) (str : string) : string =
  let n = String.length pre in
  let m = String.length str in
  if String.starts_with ~prefix:pre str then
    (String.sub str n (m - n))
  else
    str

let replace (c, s : char * string) (str : string) : string =
  let xs = String.split_on_char c str in
  String.concat s xs

type binder =
  | Lambda | Pi
and term =
  (* leaves. *)
  | Const of string * param list
  | Var of string | PVar of string
  | MVar of int | Lit of literal
  (* constructors. *)
  | App of term * term
  | Exp of term * term  (* f [t] - explicit argument. *)
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
      param list * term option * term option * string option
  | Rule of
      case list
  | Require of
      string list
  | RequireAs of
      string * string  (* module path, alias *)

type signature = command list

module EO = Syntax_eo

let app_list : term -> term list -> term =
  fun t ts -> L.fold_left (fun acc t -> App (acc, t)) t ts

let app_binop : term -> (term * term) -> term =
  fun f (t1,t2) -> App (App (f,t1),t2)

let rec app_arr : term list -> term =
  function (* return `t1 ⤳ ... ⤳ tn` *)
  | [] -> failwith "No arrow type from empty list."
  | t::[] -> t
  | t::ts -> app_binop (Var "⤳") (t, app_arr ts)

let is_var = (function Var _ -> true | PVar _ -> true | _ -> false)
let is_pi = (function Bind (Pi, _, _) -> true | _ -> false)

let in_params (s : string) (ps : param list) : bool =
  List.exists (fun (s',_,_) -> s = s') ps

let map_param (f : term -> term) : param -> param =
  function (s,t,att) -> (s,f t,att)

let rec map_vars (f : string -> term) : term -> term =
  function
  | Lit _ | PVar _ | MVar _ as t -> t
  | Const (s, ps) ->
      Const (s, L.map (map_param @@ map_vars f) ps)
  | Var s -> f s
  | App (t,t') ->
      App (map_vars f t, map_vars f t')
  | Exp (t,t') ->
      Exp (map_vars f t, map_vars f t')
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

(* Check if term is an infix operator application *)
let is_star_app = function
  | App (App (Var "∗", _), _) -> true
  | _ -> false

let is_arrow_app = function
  | App (App (Var "⤳", _), _) -> true
  | App (App (Var "⤳d", _), _) -> true
  | _ -> false

let rec term_str : term -> string =
  function
  (* HACK: τ eo.Type renders as Set for readability *)
  | App (Var "τ", Var "eo.Type") -> "Set"
  | Var ("eo.List__nil") -> "∎"

  | Const (s, ps) -> s
  | MVar i -> "?" ^ (string_of_int i)
  | Lit l -> literal_str l
  | PVar s -> "$" ^ s
  | Var s -> s

  (* ∗ is left-associative: (a ∗ b) ∗ c prints as a ∗ b ∗ c
     Left child: no parens needed for ∗ (same precedence, left-assoc)
     Right child: needs parens if it's ∗ or lower precedence *)
  | App (App (Var "⋅", t1), t2) ->
    let s1 = if is_arrow_app t1 then Printf.sprintf "(%s)" (term_str t1) else term_str t1 in
    let s2 = if is_star_app t2 || is_arrow_app t2 then Printf.sprintf "(%s)" (term_str t2) else term_str_arg t2 in
    Printf.sprintf "%s ⋅ %s" s1 s2

  | App (App (Var "eo.List__cons", t1), t2) ->
    let s1 = if is_arrow_app t1 || is_star_app t1 then Printf.sprintf "(%s)" (term_str t1) else term_str_arg t1 in
    let s2 = if is_star_app t2 then Printf.sprintf "(%s)" (term_str t2) else term_str t2 in
    Printf.sprintf "%s ⨾ %s" s1 s2

  (* ⤳ is right-associative with precedence 20, ∗ has precedence 5.
     Higher precedence binds tighter in LambdaPi, so ⤳ binds tighter than ∗.
     This means: a ⤳ b ∗ c parses as (a ⤳ b) ∗ c, NOT a ⤳ (b ∗ c).
     So when right child is ∗, we MUST parenthesize it. *)
  | App (App (Var "⤳", t1), t2) ->
    let s1 = if is_arrow_app t1 || is_star_app t1 then Printf.sprintf "(%s)" (term_str t1) else term_str_arg t1 in
    let s2 = if is_star_app t2 then Printf.sprintf "(%s)" (term_str t2) else term_str t2 in
    Printf.sprintf "%s ⤳ %s" s1 s2

  (* ⤳d is the dependent arrow - also infix, right-associative *)
  | App (App (Var "⤳d", t1), t2) ->
    let s1 = if is_arrow_app t1 || is_star_app t1 then Printf.sprintf "(%s)" (term_str t1) else term_str_arg t1 in
    let s2 = if is_star_app t2 then Printf.sprintf "(%s)" (term_str t2) else term_str t2 in
    Printf.sprintf "%s ⤳d %s" s1 s2

  | App (t, t') ->
    Printf.sprintf "%s %s" (term_str t) (term_str_arg t')

  | Exp (t, t') ->
    Printf.sprintf "%s [%s]" (term_str t) (term_str t')

  | Arrow (t, t') ->
    Printf.sprintf "(%s → %s)"
      (term_str t) (term_str t')
  | Bind (b,xs,t)->
    Printf.sprintf "(%s %s, %s)"
      (binder_str b)
      (S.concat_map " " param_str xs)
      (term_str t)
  | Let (s,t,t') ->
    Printf.sprintf "let %s ≔ %s in %s"
      s (term_str t) (term_str t')

(* Print a term as an argument - parenthesize if needed *)
and term_str_arg : term -> string = function
  | (Var _ | Lit _ | PVar _ | MVar _) as t -> term_str t
  | t -> Printf.sprintf "(%s)" (term_str t)
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
  | Symbol (m_opt, str, xs, ty_opt, def_opt, _) ->
    let m_str = match m_opt with
      | None -> ""
      | Some m -> modifier_str m ^ " "
    in
    let params_str = S.concat " " (L.map param_str xs) in
    let ty_str = match ty_opt with
      | None -> ""
      | Some ty -> ": " ^ (term_str ty)
    in
    let def_str = match def_opt with
      | None -> ""
      | Some def -> " ≔ " ^ (term_str def)
    in
    Printf.sprintf "%ssymbol %s %s%s%s;" m_str str params_str ty_str def_str
  | Rule cs ->
    let case_strs = L.map case_str cs in
    Printf.sprintf "rule %s;" (S.concat "\nwith " case_strs)
  | Require ps ->
    Printf.sprintf "require open %s;" (String.concat " " ps)
  | RequireAs (path, alias) ->
    Printf.sprintf "require %s as %s;" path alias

let sig_str : signature -> string =
  S.concat_map "\n\n" command_str
