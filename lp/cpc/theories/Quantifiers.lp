require open cpc.Core Stdlib.Set cpc.programs.Utils cpc.programs.Nary cpc.theories.Arith;
constant symbol forall : τ ({|@List|} ⤳ Bool ⤳ Bool);
constant symbol exists : τ ({|@List|} ⤳ Bool ⤳ Bool);
sequential symbol !get_var_list : τ (Bool ⤳ {|@List|});
rule !get_var_list ($Q ($xs) ($G)) ↪ $xs;
constant symbol {|@quantifiers_skolemize|} (F : τ Bool) (i : τ Int): τ (!assoc_nil_nth_type {|@list|} (!get_var_list F) i);
