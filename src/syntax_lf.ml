module L = List
module S = String
module EO = Syntax_eo
module LP = Syntax_lp

type level = EO.level
type term =
  | Sym of string * term list
  | MVar of term
  | Lit of EO.literal
  | App of term * term list
  | Let of string * term * term

let app_delim_str : level -> string =
  function
    | Tm -> " ⋅ "
    | Ty -> " ∗ "
    | Pg -> " "

let rec term_str : term -> string =
  function
  | Let (s,t,t') ->
  Printf.sprintf "(let %s := %s in %s)"
  s (term_str t) (term_str t')
  | Sym s -> s
  | Lit l -> EO.literal_str l
  | App (f,ts) ->
   begin match f with
    | Sym "->" ->
      let f =  fun t acc ->
        Printf.sprintf "%s ⤳ %s"
        (term_str t) acc
      in
        L.fold_right f ts ""
    | _ ->
        (term_str f) ^ S.concat " " (L.map term_str ts)
  end
