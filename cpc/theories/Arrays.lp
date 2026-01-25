require cpc.Prelude as eo;
require open cpc.theories.Builtin;

constant symbol Array : τ ({|eo::Type|} ⤳ ({|eo::Type|} ⤳ {|eo::Type|}));
constant symbol select : Π U: Set, Π T: Set, τ (Array U T ⤳ (U ⤳ T));
constant symbol store : Π U: Set, Π T: Set, τ (Array U T ⤳ (U ⤳ (T ⤳ Array U T)));
constant symbol {|@array_deq_diff|} : Π T: Set, Π U: Set, τ (Array T U) → τ (Array T U) → τ T;
