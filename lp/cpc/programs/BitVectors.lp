require open cpc.Core Stdlib.Set cpc.theories.BitVectors;
symbol !bv_sign_bit [m : τ Int] (b : τ (BitVec m))≔ (let T ≔ eo⋅⋅typeof b in (let w ≔ !bv_bitwidth T in (let wm1 ≔ eo⋅⋅add w (-1) in eo⋅⋅extract b wm1 wm1)));
symbol !bv_ones (m : τ Int)≔ eo⋅⋅to_bin m (eo⋅⋅add (!arith_eval_int_pow_2 m) (-1));
symbol !bv_to_signed_int [m : τ Int] (b : τ (BitVec m))≔ (let T ≔ eo⋅⋅typeof b in (let w ≔ !bv_bitwidth T in (let wm1 ≔ eo⋅⋅add w (-1) in (let z ≔ eo⋅⋅to_z (eo⋅⋅extract b (0) (eo⋅⋅add w (-2))) in eo⋅⋅ite (eo⋅⋅eq (!bv_sign_bit b) ()) (eo⋅⋅add (eo⋅⋅neg (!arith_eval_int_pow_2 wm1)) z) z))));
sequential symbol !bv_unfold_repeat_rec [m : τ Int] [n : τ Int]: τ ((eo⋅⋅quote n) ⤳ (BitVec m) ⤳ BitVec (eo⋅⋅mul n m));
rule !bv_unfold_repeat_rec (0) ($b) ↪ eo⋅⋅to_bin (0) (0)
with !bv_unfold_repeat_rec ($n) ($b) ↪ eo⋅⋅cons concat ($b) (!bv_unfold_repeat_rec (eo⋅⋅add ($n) (-1)) ($b));
symbol !bv_unfold_repeat [m : τ Int] (n : τ Int) (b : τ (BitVec m))≔ eo⋅⋅ite (eo⋅⋅and (eo⋅⋅is_z n) (eo⋅⋅not (eo⋅⋅is_neg n))) (!bv_unfold_repeat_rec n b) (repeat n b);
sequential symbol !bv_get_first_const_child [n : τ Int]: τ ((BitVec n) ⤳ BitVec n);
rule !bv_get_first_const_child ($f ($a) ($b)) ↪ eo⋅⋅ite (eo⋅⋅is_bin ($a)) ($a) (!bv_get_first_const_child ($b));
symbol !bv_bit_set [n : τ Int] (a : τ (BitVec n)) (i : τ Int)≔ eo⋅⋅eq (eo⋅⋅extract a i i) ();
symbol !nary_app [T : Set] [U : Set] [V : Set] (f : τ (T ⤳ U ⤳ V)) (a : τ T) (b : τ U)≔ f a (f b (eo⋅⋅nil f (eo⋅⋅typeof a)));
