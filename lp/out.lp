require Stdlib.Bool as B;

     symbol Bool ≔ B.bool;
     symbol true ≔ B.true;
     symbol false ≔ B.false;

require eo2lp.Core as eo;
symbol ▫ [x y] ≔  eo.app [x] [y];
notation ▫ infix left 5;

require open Stdlib.HOL;
constant symbol _Pair : Set → Set → Set;
constant symbol _pair [U : Set] [T : Set] : τ (U ⤳ T ⤳ (_Pair U T));
sequential symbol !pair_first [T : Set] [S : Set] : τ ((_Pair T S) ⤳ T);
rule !pair_first [$T] [$S] (_pair [$T] [$S] ▫ $t ▫ $s) ↪ $t;
sequential symbol !pair_second [T : Set] [S : Set] : τ ((_Pair T S) ⤳ S);
rule !pair_second [$T] [$S] (_pair [$T] [$S] ▫ $t ▫ $s) ↪ $s;
sequential symbol !evaluate_list : τ (eo.List ⤳ eo.List);
sequential symbol !evaluate_internal [T : Set] : τ (T ⤳ eo.List ⤳ T);
rule !evaluate_internal [$T] $t (eo.List⋅cons [$T] ▫ $tev ▫ eo.List⋅nil) ↪ $tev;
sequential symbol !get_arg_list_rec [S : Set] : τ (S ⤳ eo.List ⤳ eo.List);
rule !get_arg_list_rec [$S] ($f ▫ $x) $acc ↪ !get_arg_list_rec $f (eo.cons eo.List⋅cons $x $acc)
with !get_arg_list_rec [$S] $y $acc ↪ $acc;
sequential symbol !is_app [T : Set] [U : Set] [V : Set] : τ ((T ⤳ U) ⤳ V ⤳ Bool);
rule !is_app [$T] [$U] [$U] $f ($f ▫ $x) ↪ true
with !is_app [$T] [$U] [$V] $f ($g ▫ $x) ↪ !is_app $f $g
with !is_app [$T] [$U] [$V] $f $t ↪ false;
sequential symbol !is_var_list : τ (eo.List ⤳ Bool);
rule !is_var_list (eo.List⋅cons [$U] ▫ $x ▫ $xs) ↪ eo.ite (eo.is_var $x) (!is_var_list $xs) false
with !is_var_list eo.List⋅nil ↪ true;
constant symbol _{|result.null|} : τ Bool;
constant symbol _{|result.invalid|} : τ Bool;
sequential symbol !result_combine : τ (Bool ⤳ Bool ⤳ Bool);
rule !result_combine $b1 _{|result.null|} ↪ $b1
with !result_combine $b1 $b1 ↪ $b1
with !result_combine $b1 $b2 ↪ _{|result.invalid|};
sequential symbol !assoc_nil_has_type_rec [T : Set] [U : Set] : (τ (T ⤳ U ⤳ U)) → (τ U) → Set → (τ Bool);
rule !assoc_nil_has_type_rec [$T] [$U] $f ($f ▫ $x1 ▫ $x2) $W ↪ eo.requires_type_in (eo.typeof $x1) $W (!assoc_nil_has_type_rec $f $x2 $W)
with !assoc_nil_has_type_rec [$T] [$U] $f $nil $W ↪ true;
sequential symbol !assoc_nil_same_type [T : Set] [U : Set] : τ ((T ⤳ U ⤳ U) ⤳ U ⤳ Bool);
rule !assoc_nil_same_type [$T] [$U] $f ($f ▫ $x1 ▫ $x2) ↪ !assoc_nil_has_type_rec $f $x2 (eo.typeof $x1);
constant symbol ite [A : Set] : τ (Bool ⤳ A ⤳ A ⤳ A);
constant symbol not : τ (Bool ⤳ Bool);
constant symbol or : τ (Bool ⤳ Bool ⤳ Bool);
constant symbol and : τ (Bool ⤳ Bool ⤳ Bool);
constant symbol => : τ (Bool ⤳ Bool ⤳ Bool);
constant symbol xor : τ (Bool ⤳ Bool ⤳ Bool);
constant symbol = [A : Set] : τ (A ⤳ A ⤳ Bool);
sequential symbol !get_lambda_type : (τ eo.List) → Set → Set;
rule !get_lambda_type (eo.List⋅cons [eo.List] ▫ $x ▫ $xs) $B ↪ (eo.typeof $x) ⤳ (!get_lambda_type $xs $B)
with !get_lambda_type eo.List⋅nil $B ↪ $B;
constant symbol lambda [B : Set] (L : τ eo.List) : τ (B ⤳ (!get_lambda_type L B));
constant symbol distinct [x0 : Set] (xs : τ eo.List) : τ (eo.requires_type_out (!assoc_nil_same_type [x0] [eo.List] (eo.List⋅cons [x0]) xs) true Bool);
constant symbol {|@purify|} [A : Set] (t : τ A) : τ A;
