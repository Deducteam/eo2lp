open Syntax_eo

(*
  so we don't really need attribute judgements for
  translation, we only need them for elaboration.

  so, processing attributes should just update some map.
*)



type judgement =
  | TypeJ of string * param list * term
  | DefnJ of string * param list * defn
  | AttrJ of string * param list * attr
| LitJ  of lit_category * term
and defn =
  | Term of term
  | Cases of cases
and jlist =
  judgement list



(* TODO.
  consider eliminating `LitJ`, and make `declare-consts`
  introduce some appropriate coercion. then we can remove
  strings from judgement contructors, and then a *signature*
  can be a map from strings to sets of judgements.
*)

(* TODO. how should we account for attributed constants wrt.
  a list of parameters???
  e.g., right-assoc-nil where the op has type variables.  *)
