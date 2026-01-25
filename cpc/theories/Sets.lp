require cpc.Prelude as eo;
require open cpc.programs.Utils cpc.theories.Builtin cpc.theories.Arith cpc.theories.Datatypes;

constant symbol {|Set|} : τ ({|eo::Type|} ⤳ {|eo::Type|});
constant symbol {|set.empty|} : Π T: Set, τ ({|Set|} T);
constant symbol {|set.singleton|} : Π T: Set, τ (T ⤳ {|Set|} T);
constant symbol {|set.union|} : Π T: Set, τ ({|Set|} T ⤳ ({|Set|} T ⤳ {|Set|} T));
constant symbol {|set.inter|} : Π T: Set, τ ({|Set|} T ⤳ ({|Set|} T ⤳ {|Set|} T));
constant symbol {|set.minus|} : Π T: Set, τ ({|Set|} T ⤳ ({|Set|} T ⤳ {|Set|} T));
constant symbol {|set.member|} : Π T: Set, τ (T ⤳ ({|Set|} T ⤳ Bool));
constant symbol {|set.subset|} : Π T: Set, τ ({|Set|} T ⤳ ({|Set|} T ⤳ Bool));
constant symbol {|set.choose|} : Π T: Set, τ ({|Set|} T ⤳ T);
constant symbol {|set.is_empty|} : Π T: Set, τ ({|Set|} T ⤳ Bool);
constant symbol {|set.is_singleton|} : Π T: Set, τ ({|Set|} T ⤳ Bool);
constant symbol {|set.insert|} : Π T: Set, τ ({|eo::List|} ⤳ ({|Set|} T ⤳ {|Set|} T));
constant symbol {|@sets_deq_diff|} : Π T: Set, τ ({|Set|} T) → τ ({|Set|} T) → τ T;
