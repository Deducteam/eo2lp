require cpc.Prelude as eo;
require open cpc.programs.Utils;

sequential symbol {|$get_ai_norm_rec|} : Π T: Set, τ ((T ⤳ (T ⤳ T)) ⤳ (T ⤳ (T ⤳ T)));
sequential symbol {|$get_ai_norm|} : Π T: Set, τ (T ⤳ T);
sequential symbol {|$get_a_norm_rec|} : Π T: Set, τ ((T ⤳ (T ⤳ T)) ⤳ (T ⤳ (T ⤳ T)));
sequential symbol {|$get_a_norm|} : Π U: Set, τ (U ⤳ U);
constant symbol {|@@aci_sorted|} : Π U: Set, Π T: Set, τ (U ⤳ (T ⤳ T));
symbol {|@aci.sorted|} [U : Set] [T : Set] ≔ @{|@@aci_sorted|} U T;
sequential symbol {|$aci_norm_eq|} : Π U: Set, τ (U ⤳ (U ⤳ Bool));
symbol {|$is_aci_norm|} [S : Set] (a : τ S) (b : τ S) (an : τ S) (bn : τ S) ≔ @{|eo::ite|} Bool (?? (@APP S Bool (@APP S (S ⤳ Bool) (@{|$aci_norm_eq|} S) bn) a) Bool Bool) (@APP S Bool (@APP S (S ⤳ Bool) (@{|$aci_norm_eq|} S) an) b) true (@{|eo::ite|} Bool Bool (@APP S Bool (@APP S (S ⤳ Bool) (@{|$aci_norm_eq|} S) bn) a) true (@APP S Bool (@APP S (S ⤳ Bool) (@{|$aci_norm_eq|} S) an) bn));
