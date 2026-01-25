require cpc.Prelude as eo;
require open cpc.theories.Arith;

sequential symbol {|$assoc_nil_nth_type|} : Π T: Set, Π U: Set, Π V: Set, Π W: Set, τ ((T ⤳ (U ⤳ V)) ⤳ (W ⤳ ({|eo::Int|} ⤳ {|eo::Type|})));
