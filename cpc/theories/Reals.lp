require cpc.Prelude as eo;
require open cpc.theories.Arith;
constant symbol div [T : Set] [U : Set]: τ (T ⤳ U ⤳ eo.requires (!is_arith_type T) true (eo.requires (!is_arith_type U) true Real));
constant symbol div_total [T : Set] [U : Set]: τ (T ⤳ U ⤳ eo.requires (!is_arith_type T) true (eo.requires (!is_arith_type U) true Real));
constant symbol div_by_zero : τ (Real ⤳ Real);
