require cpc.Prelude as eo;
require open cpc.Prelude;
symbol !compare_geq [T : Set] (x : τ T) (y : τ T) ≔ eo.ite (eo.eq x y) true (eo.gt x y);
constant symbol Pair : τ (eo.Type ⤳ eo.Type ⤳ eo.Type);
constant symbol pair [U : Set] [T : Set]: τ (U ⤳ T ⤳ Pair U T);
sequential symbol !pair_first [T : Set] [S : Set]: τ ((Pair T S) ⤳ T);
rule !pair_first [$T] [$S] (pair ⋅ $t ⋅ $s) ↪ $t;
sequential symbol !pair_second [T : Set] [S : Set]: τ ((Pair T S) ⤳ S);
rule !pair_second [$T] [$S] (pair ⋅ $t ⋅ $s) ↪ $s;
sequential symbol !evaluate_list : τ (eo.List ⤳ eo.List);
sequential symbol !evaluate_internal [T : Set]: τ (T ⤳ eo.List ⤳ T);
rule !evaluate_internal [$T] $t (eo.List__cons [$T] ⋅ $tev ⋅ ∎) ↪ $tev;
symbol !evaluate [T : Set] (t : τ T) ≔ !evaluate_internal t (!evaluate_list (eo.List__cons ⋅ t ⋅ ∎));
sequential symbol !get_arg_list_rec [S : Set]: τ (S ⤳ eo.List ⤳ eo.List);
rule !get_arg_list_rec [$S] ($f ⋅ $x) $acc ↪ !get_arg_list_rec $f (eo.cons eo.List__cons $x $acc)
with !get_arg_list_rec [$S] $y $acc ↪ $acc;
symbol !get_arg_list [T : Set] (t : τ T) ≔ !get_arg_list_rec t ∎;
sequential symbol !is_app [T : Set] [U : Set] [V : Set]: τ ((T ⤳ U) ⤳ V ⤳ Bool);
rule !is_app [$T] [$U] [$V] $f ($f ⋅ $x) ↪ true
with !is_app [$T] [$U] [$V] $f ($g ⋅ $x) ↪ !is_app $f $g
with !is_app [$T] [$U] [$V] $f $t ↪ false;
sequential symbol !is_var_list : τ (eo.List ⤳ Bool);
rule !is_var_list (eo.List__cons [$U] ⋅ $x ⋅ $xs) ↪ eo.ite (eo.is_var $x) (!is_var_list $xs) false
with !is_var_list ∎ ↪ true;
symbol !compare_var [T : Set] [U : Set] (a : τ T) (b : τ U) ≔ eo.cmp b a;
constant symbol result_null : τ Bool;
constant symbol result_invalid : τ Bool;
sequential symbol !result_combine : τ (Bool ⤳ Bool ⤳ Bool);
rule !result_combine $b1 result_null ↪ $b1
with !result_combine $b1 $b1 ↪ $b1
with !result_combine $b1 $b2 ↪ result_invalid;
sequential symbol !assoc_nil_has_type_rec [T : Set] [U : Set]: τ ((T ⤳ U ⤳ U) ⤳ U ⤳ eo.Type ⤳ Bool);
rule !assoc_nil_has_type_rec [$T] [$U] $f ($f ⋅ $x1 ⋅ $x2) $W ↪ eo.requires (eo.typeof $x1) $W (!assoc_nil_has_type_rec $f $x2 $W)
with !assoc_nil_has_type_rec [$T] [$U] $f $nil $W ↪ true;
sequential symbol !assoc_nil_same_type [T : Set] [U : Set]: τ ((T ⤳ U ⤳ U) ⤳ U ⤳ Bool);
rule !assoc_nil_same_type [$T] [$U] $f ($f ⋅ $x1 ⋅ $x2) ↪ !assoc_nil_has_type_rec $f $x2 (eo.typeof $x1);
