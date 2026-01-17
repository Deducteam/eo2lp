require open
  Stdlib.Set
  Stdlib.HOL
  Stdlib.List
  Stdlib.String
  Stdlib.Z
  Stdlib.Bool;

symbol eo⋅⋅Type : Set;
rule τ eo⋅⋅Type ↪ Set;

symbol !compare_geq [T : Set] (x : τ T) (y : τ T)≔ eo⋅⋅ite (eo⋅⋅eq x y) true (eo⋅⋅gt x y);
constant symbol _Pair : τ (eo⋅⋅Type ⤳ eo⋅⋅Type ⤳ eo⋅⋅Type);
symbol {|@Pair|} ≔ _Pair;
constant symbol _pair [U : Set] [T : Set]: τ (U ⤳ T ⤳ {|@Pair|} U T);
symbol {|@pair|} ≔ _pair;
sequential symbol !pair_first [T : Set] [S : Set]: τ (({|@Pair|} T S) ⤳ T);
rule !pair_first ({|@pair|} ($t) ($s)) ↪ $t;
sequential symbol !pair_second [T : Set] [S : Set]: τ (({|@Pair|} T S) ⤳ S);
rule !pair_second ({|@pair|} ($t) ($s)) ↪ $s;
symbol {|@List|} ≔ eo⋅⋅List;
symbol {|@list.nil|} ≔ eo⋅⋅List⋅⋅nil;
symbol {|@list|} ≔ eo⋅⋅List⋅⋅cons;
sequential symbol !evaluate_list : τ ({|@List|} ⤳ {|@List|});
rule ;
sequential symbol !evaluate_internal [T : Set]: τ (T ⤳ {|@List|} ⤳ T);
rule !evaluate_internal ($t) ({|@list|} ($tev)) ↪ $tev;
symbol !evaluate [T : Set] (t : τ T)≔ !evaluate_internal t (!evaluate_list ({|@list|} t));
sequential symbol !get_arg_list_rec [S : Set]: τ (S ⤳ {|@List|} ⤳ {|@List|});
rule !get_arg_list_rec ($f ($x)) ($acc) ↪ !get_arg_list_rec ($f) (eo⋅⋅cons {|@list|} ($x) ($acc))
with !get_arg_list_rec ($y) ($acc) ↪ $acc;
symbol !get_arg_list [T : Set] (t : τ T)≔ !get_arg_list_rec t {|@list.nil|};
sequential symbol !is_app [T : Set] [U : Set] [V : Set]: τ ((T ⤳ U) ⤳ V ⤳ Bool);
rule !is_app ($f) ($f ($x)) ↪ true
with !is_app ($f) ($g ($x)) ↪ !is_app ($f) ($g)
with !is_app ($f) ($t) ↪ false;
sequential symbol !is_var_list : τ ({|@List|} ⤳ Bool);
rule !is_var_list ({|@list|} ($x) ($xs)) ↪ eo⋅⋅ite (eo⋅⋅is_var ($x)) (!is_var_list ($xs)) false
with !is_var_list {|@list.nil|} ↪ true;
symbol !compare_var [T : Set] [U : Set] (a : τ T) (b : τ U)≔ eo⋅⋅cmp b a;
constant symbol _result⋅null : τ Bool;
symbol {|@result.null|} ≔ _result⋅null;
constant symbol _result⋅invalid : τ Bool;
symbol {|@result.invalid|} ≔ _result⋅invalid;
sequential symbol !result_combine : τ (Bool ⤳ Bool ⤳ Bool);
rule !result_combine ($b1) {|@result.null|} ↪ $b1
with !result_combine ($b1) ($b1) ↪ $b1
with !result_combine ($b1) ($b2) ↪ {|@result.invalid|};
sequential symbol !assoc_nil_has_type_rec [T : Set] [U : Set]: τ ((T ⤳ U ⤳ U) ⤳ U ⤳ eo⋅⋅Type ⤳ Bool);
rule !assoc_nil_has_type_rec ($f) ($f ($x1) ($x2)) ($W) ↪ eo⋅⋅requires (eo⋅⋅typeof ($x1)) ($W) (!assoc_nil_has_type_rec ($f) ($x2) ($W))
with !assoc_nil_has_type_rec ($f) ($nil) ($W) ↪ true;
sequential symbol !assoc_nil_same_type [T : Set] [U : Set]: τ ((T ⤳ U ⤳ U) ⤳ U ⤳ Bool);
rule !assoc_nil_same_type ($f) ($f ($x1) ($x2)) ↪ !assoc_nil_has_type_rec ($f) ($x2) (eo⋅⋅typeof ($x1));
