require open cpc.Core Stdlib.Set cpc.theories.Arith;
constant symbol / [T : Set] [U : Set]: τ (T ⤳ U ⤳ eo⋅⋅requires (!is_arith_type T) true (eo⋅⋅requires (!is_arith_type U) true Real));
constant symbol /_total [T : Set] [U : Set]: τ (T ⤳ U ⤳ eo⋅⋅requires (!is_arith_type T) true (eo⋅⋅requires (!is_arith_type U) true Real));
constant symbol {|@div_by_zero|} : τ (Real ⤳ Real);
