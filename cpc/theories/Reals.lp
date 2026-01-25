require cpc.Prelude as eo;
require open cpc.theories.Arith;

constant symbol {|/|} : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true (@{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} U) true {|eo::Rat|})));
constant symbol {|/_total|} : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true (@{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} U) true {|eo::Rat|})));
constant symbol {|@div_by_zero|} : τ ({|eo::Rat|} ⤳ {|eo::Rat|});
