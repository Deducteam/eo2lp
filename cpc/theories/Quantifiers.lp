require cpc.Prelude as eo;
require open cpc.programs.Utils cpc.programs.Nary cpc.theories.Arith;
constant symbol forall : τ (eo.List ⤳ Bool ⤳ Bool);
constant symbol exists : τ (eo.List ⤳ Bool ⤳ Bool);
sequential symbol !get_var_list : τ (Bool ⤳ eo.List);
rule !get_var_list ($Q ⋅ $xs ⋅ $G) ↪ $xs;
constant symbol quantifiers_skolemize [v0 : Set] (F : τ Bool) (i : τ Int): τ (!assoc_nil_nth_type (eo.List__cons [v0]) (!get_var_list F) i);
