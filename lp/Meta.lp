require open eo2lp.Core;
require open Stdlib.List;

symbol eo : Set;
symbol Symbol : τ (string ⤳ eo);
symbol Apply : τ (list eo ⤳ eo);

inductive Attr : TYPE ≔
  | RightAssocNil : Attr
  ;
