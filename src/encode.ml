module LF = Syntax_lf
module LP = Syntax_lp

open Literal

module S = String
module L = List

let strip_prefix (str : string) (pre : string) : string =
  let n = String.length pre in
  let m = String.length str in
  (String.sub str n (m - n))

let replace (c, s : char * string) (str : string) : string =
  let xs = String.split_on_char c str in
  String.concat s xs

let rec safe_name : string -> string =
  function
  | s when S.starts_with ~prefix:"$" s ->
    "!" ^ safe_name (strip_prefix s "$")
  | s when S.starts_with ~prefix:"@@" s ->
    "_" ^ safe_name (strip_prefix s "@@")
  | s when S.starts_with ~prefix:"eo::" s ->
    "eo." ^ safe_name (strip_prefix s "eo::")
  | s ->
    let s' = s |> replace ('.',"⋅") |> replace (':', "⋅") in
    if LP.is_forbidden s'
      then Printf.sprintf "{|%s|}" s
      else s'

type level = Tm | Ty
let lv_app
  (lv : level) (t,t' : LP.term * LP.term) : LP.term =
  match lv with
  | Tm -> LP.app_list (Var "◽") [t;t']
  | Ty -> LP.app_list (Var "☆") [t;t']

let _El : LP.term -> LP.term =
  fun t -> App (Var "El", t)

let rec encode_tm : LF.term -> LP.term =
  function
  | Const (s,ts) ->
      LP.app_list (Var (safe_name s)) (L.map encode_tm ts)
  | Var s -> Var (safe_name s)
  | Lit l -> Var (literal_str l)
  | App (t,t') -> App (encode_tm t, encode_tm t')
  | Let (s,t,t') -> Let (s, encode_tm t, encode_tm t')

let rec encode_prm : LF.param list -> LP.param list =
  function
  | [] -> []
  | (s,t,a) :: ps ->
    let a' =
      if a = Implicit then LP.Implicit else LP.Explicit
    in
      (safe_name s, _El (encode_tm t), a') :: encode_prm ps

let encode_cs : LF.case list -> LP.case list =
  L.map (fun (t,t') -> encode_tm t, encode_tm t')

let encode_sym : (string * LF.symbol) -> LP.command list =
  function
  | s, Decl (ps, t) ->
    [
      Symbol (
        Some Constant,
        safe_name s,
        encode_prm ps,
        Some (_El (encode_tm t)),
        None
      )
    ]
  | s, Prog ((ps,t), (qs, cs)) ->
      Symbol (
        Some Sequential,
        safe_name s,
        encode_prm ps,
        Some (_El (encode_tm t)),
        None
      )
    :: (if cs = [] then [] else [Rule (encode_cs cs)])
