require open cpc.Core Stdlib.Set cpc.theories.Builtin cpc.theories.Reals cpc.theories.Ints cpc.programs.Arith cpc.programs.Utils cpc.programs.PolyNorm;
sequential symbol !arith_rel_sum [T : Set] [U : Set] [V : Set] [W : Set]: τ (T ⤳ U ⤳ V ⤳ W ⤳ Bool);
rule !arith_rel_sum < < ($a) ($b) ↪ and (< ($a) ($b))
with !arith_rel_sum < = ($a) ($b) ↪ and (< ($a) ($b))
with !arith_rel_sum < <= ($a) ($b) ↪ and (< ($a) ($b))
with !arith_rel_sum <= < ($a) ($b) ↪ and (< ($a) ($b))
with !arith_rel_sum <= = ($a) ($b) ↪ and (<= ($a) ($b))
with !arith_rel_sum <= <= ($a) ($b) ↪ and (<= ($a) ($b))
with !arith_rel_sum = < ($a) ($b) ↪ and (< ($a) ($b))
with !arith_rel_sum = = ($a) ($b) ↪ and (<= ($a) ($b))
with !arith_rel_sum = <= ($a) ($b) ↪ and (<= ($a) ($b));
sequential symbol !mk_arith_sum_ub : τ (Bool ⤳ Bool ⤳ Bool);
rule !mk_arith_sum_ub true ($acc) ↪ $acc
with !mk_arith_sum_ub (and ($r1 ($a1) ($b1)) ($tail)) ($r2 ($a2) ($b2)) ↪ !mk_arith_sum_ub ($tail) (!arith_rel_sum ($r1) ($r2) (+ ($a1) ($a2)) (+ ($b1) ($b2)));
sequential symbol !mk_arith_mult_pos [S : Set]: τ (S ⤳ Bool ⤳ Bool);
rule !mk_arith_mult_pos ($m) ($r ($a) ($b)) ↪ $r (* ($m) (* ($a) (1))) (* ($m) (* ($b) (1)));
sequential symbol !arith_rel_inv [T : Set] [U : Set] [V : Set]: τ (T ⤳ U ⤳ V ⤳ Bool);
rule !arith_rel_inv = ($a) ($b) ↪ and (= ($a) ($b))
with !arith_rel_inv < ($a) ($b) ↪ and (> ($a) ($b))
with !arith_rel_inv <= ($a) ($b) ↪ and (>= ($a) ($b))
with !arith_rel_inv > ($a) ($b) ↪ and (< ($a) ($b))
with !arith_rel_inv >= ($a) ($b) ↪ and (<= ($a) ($b));
sequential symbol !mk_arith_mult_neg [S : Set]: τ (S ⤳ Bool ⤳ Bool);
rule !mk_arith_mult_neg ($m) ($r ($a) ($b)) ↪ !arith_rel_inv ($r) (* ($m) (* ($a) (1))) (* ($m) (* ($b) (1)));
sequential symbol !arith_rel_trichotomy [T : Set] [U : Set] [V : Set] [W : Set]: τ (T ⤳ U ⤳ V ⤳ W ⤳ Bool);
rule !arith_rel_trichotomy = < ($a) ($b) ↪ and (> ($a) ($b))
with !arith_rel_trichotomy = > ($a) ($b) ↪ and (< ($a) ($b))
with !arith_rel_trichotomy > = ($a) ($b) ↪ and (< ($a) ($b))
with !arith_rel_trichotomy < = ($a) ($b) ↪ and (> ($a) ($b))
with !arith_rel_trichotomy > < ($a) ($b) ↪ and (= ($a) ($b))
with !arith_rel_trichotomy < > ($a) ($b) ↪ and (= ($a) ($b));
sequential symbol !arith_rel_neg [T : Set] [U : Set] [V : Set]: τ (T ⤳ U ⤳ V ⤳ Bool);
rule !arith_rel_neg < ($a) ($b) ↪ and (>= ($a) ($b))
with !arith_rel_neg <= ($a) ($b) ↪ and (> ($a) ($b))
with !arith_rel_neg > ($a) ($b) ↪ and (<= ($a) ($b))
with !arith_rel_neg >= ($a) ($b) ↪ and (< ($a) ($b));
sequential symbol !arith_normalize_lit : τ (Bool ⤳ Bool);
rule !arith_normalize_lit (not (not ($r ($a) ($b)))) ↪ $r ($a) ($b)
with !arith_normalize_lit (not ($r ($a) ($b))) ↪ !arith_rel_neg ($r) ($a) ($b)
with !arith_normalize_lit ($r ($a) ($b)) ↪ $r ($a) ($b);
sequential symbol !mk_arith_trichotomy : τ (Bool ⤳ Bool ⤳ Bool);
rule !mk_arith_trichotomy ($r1 ($a) ($b)) ($r2 ($a) ($b)) ↪ !arith_rel_trichotomy ($r1) ($r2) ($a) ($b);
sequential symbol !greatest_int_lt [R : Set]: τ (R ⤳ Int);
rule !greatest_int_lt ($c) ↪ (let ci ≔ eo⋅⋅to_z ($c) in eo⋅⋅ite (eo⋅⋅eq (eo⋅⋅to_q ($c)) (eo⋅⋅to_q ci)) (eo⋅⋅add (-1) ci) ci);
sequential symbol !least_int_gt [R : Set]: τ (R ⤳ Int);
rule !least_int_gt ($c) ↪ eo⋅⋅add (1) (eo⋅⋅to_z ($c));
sequential symbol !strip_even_exponent [T : Set] [U : Set]: τ (T ⤳ U ⤳ U);
rule !strip_even_exponent ($t) (* ($t) (* ($t) (eo⋅⋅list_concat * ($m) (1)))) ↪ !strip_even_exponent ($t) ($m)
with !strip_even_exponent ($t) ($m) ↪ $m;
sequential symbol !mk_arith_mult_sign_sgn [T : Set]: τ (Bool ⤳ Bool ⤳ T ⤳ Bool);
rule !mk_arith_mult_sign_sgn ($sgn) (and (not (and (= ($t) ($z)))) ($F)) (* ($t) (* ($t) (eo⋅⋅list_concat * ($m) (1)))) ↪ eo⋅⋅requires (eo⋅⋅to_z ($z)) (0) (!mk_arith_mult_sign_sgn ($sgn) ($F) (!strip_even_exponent ($t) ($m)))
with !mk_arith_mult_sign_sgn ($sgn) (and (and (> ($t) ($z))) ($F)) (* ($t) ($m)) ↪ eo⋅⋅requires (eo⋅⋅to_z ($z)) (0) (!mk_arith_mult_sign_sgn ($sgn) ($F) (!strip_even_exponent ($t) ($m)))
with !mk_arith_mult_sign_sgn ($sgn) (and (and (< ($t) ($z))) ($F)) (* ($t) ($m)) ↪ eo⋅⋅requires (eo⋅⋅to_z ($z)) (0) (!mk_arith_mult_sign_sgn (eo⋅⋅not ($sgn)) ($F) (!strip_even_exponent ($t) ($m)))
with !mk_arith_mult_sign_sgn ($sgn) true (1) ↪ $sgn
with !mk_arith_mult_sign_sgn ($sgn) ($l) ($m) ↪ !mk_arith_mult_sign_sgn ($sgn) (and ($l)) ($m);
sequential symbol !mk_arith_mult_abs_comparison_rec : τ (Bool ⤳ Bool ⤳ Bool);
rule !mk_arith_mult_abs_comparison_rec (and ($r (abs ($t)) (abs ($u))) ($B)) ($r ($a) ($b)) ↪ !mk_arith_mult_abs_comparison_rec ($B) ($r (eo⋅⋅list_concat * ($a) (* ($t) (1))) (eo⋅⋅list_concat * ($b) (* ($u) (1))))
with !mk_arith_mult_abs_comparison_rec (and (and (and (= (abs ($t)) (abs ($u)))) (not (and (= ($t) ($z))))) ($B)) (and (> ($a) ($b))) ↪ eo⋅⋅requires (eo⋅⋅to_z ($z)) (0) (!mk_arith_mult_abs_comparison_rec ($B) (and (> (eo⋅⋅list_concat * ($a) (* ($t) (1))) (eo⋅⋅list_concat * ($b) (* ($u) (1))))))
with !mk_arith_mult_abs_comparison_rec true ($r ($a) ($b)) ↪ $r (abs ($a)) (abs ($b));
sequential symbol !mk_arith_mult_abs_comparison : τ (Bool ⤳ Bool);
rule !mk_arith_mult_abs_comparison (and (and (> (abs ($t)) (abs ($u)))) ($B)) ↪ !mk_arith_mult_abs_comparison_rec ($B) (and (> (* ($t) (1)) (* ($u) (1))))
with !mk_arith_mult_abs_comparison (and (and (= (abs ($t)) (abs ($u)))) ($B)) ↪ !mk_arith_mult_abs_comparison_rec ($B) (and (= (* ($t) (1)) (* ($u) (1))));
symbol !arith_to_int_reduction (r : τ Real)≔ (let k ≔ {|@purify|} (to_int r) in and (and (<= (0/1) (- r (to_real k)))) (and (< (- r (to_real k)) (1/1))));
symbol !arith_int_div_total_reduction (u : τ Int) (v : τ Int)≔ (let k ≔ {|@purify|} (div_total u v) in (let lb ≔ and (<= (* v (* k (1))) u) in eo⋅⋅ite (eo⋅⋅is_z v) (eo⋅⋅requires (eo⋅⋅eq v (0)) false (and lb (and (< u (* v (* (+ k (+ (eo⋅⋅ite (eo⋅⋅is_neg v) (-1) (1)) (0))) (1))))))) (and (=> (and (> v (0))) (and lb (and (< u (* v (* (+ k (+ (1) (0))) (1))))))) (=> (and (< v (0))) (and lb (and (< u (* v (* (+ k (+ (-1) (0))) (1))))))))));
symbol !arith_int_log2_reduction (u : τ Int)≔ (let k ≔ {|@purify|} (int⋅log2 u) in (let i ≔ and (< (0) u) in and (=> i (and (and (<= (int⋅pow2 k) u)) (and (< u (int⋅pow2 (+ k (+ (1) (0)))))))) (=> (not i) (and (= k (0))))));
sequential symbol !arith_reduction_pred [T : Set]: τ (T ⤳ Bool);
rule !arith_reduction_pred (is_int ($u)) ↪ (let k ≔ {|@purify|} (to_int ($u)) in and (and (= (is_int ($u)) (and (= ($u) (to_real k))))) (!arith_to_int_reduction ($u)))
with !arith_reduction_pred (to_int ($u)) ↪ (let k ≔ {|@purify|} (to_int ($u)) in and (and (= (to_int ($u)) k)) (!arith_to_int_reduction ($u)))
with !arith_reduction_pred (/ ($u) ($v)) ↪ (let ur ≔ eo⋅⋅ite (eo⋅⋅eq (eo⋅⋅typeof ($u)) Int) (to_real ($u)) ($u) in and (= (/ ($u) ($v)) (ite (and (= ($v) (!arith_mk_zero (eo⋅⋅typeof ($v))))) ({|@div_by_zero|} ur) (/_total ($u) ($v)))))
with !arith_reduction_pred (div ($a) ($b)) ↪ and (= (div ($a) ($b)) (ite (and (= ($b) (0))) ({|@int_div_by_zero|} ($a)) (div_total ($a) ($b))))
with !arith_reduction_pred (mod ($a) ($b)) ↪ and (= (mod ($a) ($b)) (ite (and (= ($b) (0))) ({|@mod_by_zero|} ($a)) (mod_total ($a) ($b))))
with !arith_reduction_pred (/_total ($u) ($v)) ↪ (let k ≔ {|@purify|} (/_total ($u) ($v)) in (let ur ≔ eo⋅⋅ite (eo⋅⋅eq (eo⋅⋅typeof ($u)) Int) (to_real ($u)) ($u) in and (and (= (/_total ($u) ($v)) k)) (=> (not (and (= ($v) (!arith_mk_zero (eo⋅⋅typeof ($v)))))) (and (= (* ($v) (* k (1))) ur)))))
with !arith_reduction_pred (div_total ($a) ($b)) ↪ (let k ≔ {|@purify|} (div_total ($a) ($b)) in and (and (= (div_total ($a) ($b)) k)) (!arith_int_div_total_reduction ($a) ($b)))
with !arith_reduction_pred (mod_total ($a) ($b)) ↪ (let k ≔ {|@purify|} (div_total ($a) ($b)) in and (and (= (mod_total ($a) ($b)) (- ($a) (* ($b) (* k (1)))))) (!arith_int_div_total_reduction ($a) ($b)))
with !arith_reduction_pred (abs ($u)) ↪ and (= (abs ($u)) (ite (and (< ($u) (!arith_mk_zero (eo⋅⋅typeof ($u))))) (- ($u)) ($u)))
with !arith_reduction_pred (int⋅log2 ($u)) ↪ (let k ≔ {|@purify|} (int⋅log2 ($u)) in and (and (= (int⋅log2 ($u)) k)) (!arith_int_log2_reduction ($u)));
sequential symbol !is_poly_norm_rel_consts : τ (Bool ⤳ Bool);
rule !is_poly_norm_rel_consts (and (< ($cx) ($cy))) ↪ eo⋅⋅eq (!sgn ($cx)) (!sgn ($cy))
with !is_poly_norm_rel_consts (and (<= ($cx) ($cy))) ↪ eo⋅⋅eq (!sgn ($cx)) (!sgn ($cy))
with !is_poly_norm_rel_consts (and (= ($cx) ($cy))) ↪ true
with !is_poly_norm_rel_consts (and (>= ($cx) ($cy))) ↪ eo⋅⋅eq (!sgn ($cx)) (!sgn ($cy))
with !is_poly_norm_rel_consts (and (> ($cx) ($cy))) ↪ eo⋅⋅eq (!sgn ($cx)) (!sgn ($cy))
with !is_poly_norm_rel_consts ($b) ↪ false;
sequential symbol !is_eq_maybe_to_real [U : Set] [T : Set]: τ (U ⤳ T ⤳ Bool);
rule !is_eq_maybe_to_real ($x) ($x) ↪ true
with !is_eq_maybe_to_real (to_real ($x)) ($x) ↪ true;
