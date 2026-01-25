require cpc.Prelude as eo;
require open cpc.Prelude;

symbol {|$compare_geq|} [T : τ {|eo::Type|}] (x : τ T) (y : τ T) ≔ @{|eo::ite|} Bool Bool (@{|eo::eq|} T T x y) true (@{|eo::gt|} T T x y);
constant symbol {|@@Pair|} : τ ({|eo::Type|} ⤳ ({|eo::Type|} ⤳ {|eo::Type|}));
constant symbol {|@@pair|} : τ (Π U: τ {|eo::Type|}, Π T: τ {|eo::Type|}, U ⤳ (T ⤳ {|@@Pair|} U T));
sequential symbol {|$pair_first|} : τ {|eo::Type|} → τ {|eo::Type|} → τ {|eo::Type|} → {|@@Pair|} T S ⤳ T;
sequential symbol {|$pair_second|} : τ {|eo::Type|} → τ {|eo::Type|} → τ {|eo::Type|} → {|@@Pair|} T S ⤳ S;
sequential symbol {|$is_app|} : τ {|eo::Type|} → τ {|eo::Type|} → τ {|eo::Type|} → (T ⤳ U) ⤳ (V ⤳ Bool);
symbol {|$compare_var|} [T : τ {|eo::Type|}] [U : τ {|eo::Type|}] (a : τ T) (b : τ U) ≔ @{|eo::cmp|} U T b a;
constant symbol {|@@result.null|} : τ Bool;
constant symbol {|@@result.invalid|} : τ Bool;
sequential symbol {|$result_combine|} : Bool ⤳ (Bool ⤳ Bool);
sequential symbol {|$assoc_nil_has_type_rec|} : τ {|eo::Type|} → τ {|eo::Type|} → τ {|eo::Type|} → τ {|eo::Type|} → (T ⤳ (U ⤳ U)) ⤳ (U ⤳ ({|eo::Type|} ⤳ Bool));
sequential symbol {|$assoc_nil_same_type|} : τ {|eo::Type|} → τ {|eo::Type|} → τ {|eo::Type|} → τ {|eo::Type|} → (T ⤳ (U ⤳ U)) ⤳ (U ⤳ Bool);
