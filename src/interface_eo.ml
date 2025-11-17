open Syntax_eo

type defn =
  | Term of term
  | Cases of (term * term) list

type judgement =
  | TypeJ of symbol * param list * term
  | DefnJ of symbol * param list * defn
  | AttrJ of symbol * param list * attr
