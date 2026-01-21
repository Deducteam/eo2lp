require cpc.Prelude as eo;
require open cpc.theories.Ints cpc.theories.Arith cpc.programs.Utils;
symbol !sgn [T : Set] (x : τ T) ≔ eo.ite (eo.is_neg x) -1 (eo.ite (eo.is_neg (eo.neg x)) 1 0);
symbol !arith_mk_zero (T : Set) ≔ eo.ite (eo.is_eq T Int) 0 (eo.requires T Real (mkrat 0 1));
symbol !arith_eval_add [T : Set] [U : Set] (x : τ T) (y : τ U) ≔ let xq ≔ eo.to_q x in let yq ≔ eo.to_q y in eo.ite (eo.eq x xq) (eo.add xq yq) (eo.ite (eo.eq y yq) (eo.add xq yq) (eo.add x y));
symbol !arith_eval_sub [U : Set] [T : Set] (x : τ U) (y : τ T) ≔ !arith_eval_add x (eo.neg y);
symbol !arith_eval_mul [T : Set] [U : Set] (x : τ T) (y : τ U) ≔ let xq ≔ eo.to_q x in let yq ≔ eo.to_q y in eo.ite (eo.eq x xq) (eo.mul xq yq) (eo.ite (eo.eq y yq) (eo.mul xq yq) (eo.mul x y));
symbol !arith_eval_qsub [U : Set] [T : Set] (x : τ U) (y : τ T) ≔ eo.add (eo.to_q x) (eo.neg (eo.to_q y));
symbol !arith_mk_binary_minus [T : Set] [U : Set] (x : τ T) (y : τ U) ≔ - ⋅ x ⋅ y;
sequential symbol !arith_eval_int_log_2_rec : τ (Int ⤳ Int);
rule !arith_eval_int_log_2_rec 1 ↪ 0
with !arith_eval_int_log_2_rec $x ↪ eo.add 1 (!arith_eval_int_log_2_rec (eo.zdiv $x 2));
symbol !arith_eval_int_log_2 (x : τ Int) ≔ eo.ite (eo.is_neg (eo.neg x)) (!arith_eval_int_log_2_rec x) 0;
sequential symbol !arith_eval_int_pow_2_rec : τ (Int ⤳ Int);
rule !arith_eval_int_pow_2_rec 0 ↪ 1
with !arith_eval_int_pow_2_rec $x ↪ eo.mul 2 (!arith_eval_int_pow_2_rec (eo.add $x -1));
symbol !arith_eval_int_pow_2 (x : τ Int) ≔ eo.ite (eo.is_z x) (eo.ite (eo.is_neg x) 0 (!arith_eval_int_pow_2_rec x)) (int_pow2 ⋅ x);
symbol !arith_eval_int_is_pow_2 (x : τ Int) ≔ eo.ite (eo.is_z x) (eo.ite (eo.is_neg x) false (eo.eq x (!arith_eval_int_pow_2 (!arith_eval_int_log_2 x)))) (int_ispow2 ⋅ x);
