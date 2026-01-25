require cpc.Prelude as eo;
require open cpc.programs.Nary;

constant symbol is : Π C: Set, Π D: Set, τ (C ⤳ (D ⤳ Bool));
constant symbol update : Π D: Set, Π T: Set, Π S: Set, τ (S ⤳ (D ⤳ (T ⤳ D)));
constant symbol UnitTuple : Set;
constant symbol Tuple : τ ({|eo::Type|} ⤳ ({|eo::Type|} ⤳ {|eo::Type|}));
constant symbol {|tuple.unit|} : τ UnitTuple;
constant symbol tuple : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @{|eo::cons|} {|eo::Type|} {|eo::Type|} Tuple T U));
constant symbol {|tuple.select|} : Π T: Set, Π i: τ {|eo::Int|}, τ (T ⤳ @{|eo::list_nth|} {|eo::Type|} {|eo::Type|} Tuple T i);
constant symbol {|tuple.update|} : Π T: Set, Π U: Set, Π i: τ {|eo::Int|}, τ (T ⤳ (U ⤳ @{|eo::requires|} {|eo::Type|} {|eo::Type|} {|eo::Type|} U (@{|eo::list_nth|} {|eo::Type|} {|eo::Type|} Tuple T i) T));
