require open cpc.Core Stdlib.Set cpc.theories.Ints cpc.theories.Reals cpc.theories.BitVectors cpc.programs.Utils;
symbol !typeunion (T : Set) (U : Set)≔ eo⋅⋅ite (eo⋅⋅eq T U) T (!arith_typeunion T U);
constant symbol _Monomial : Set;
symbol {|@Monomial|} ≔ _Monomial;
constant symbol _mon [T : Set]: τ (T ⤳ Real ⤳ {|@Monomial|});
symbol {|@mon|} ≔ _mon;
constant symbol _Polynomial : Set;
symbol {|@Polynomial|} ≔ _Polynomial;
constant symbol _poly⋅zero : τ {|@Polynomial|};
symbol {|@poly.zero|} ≔ _Polynomial;
constant symbol _poly : τ ({|@Monomial|} ⤳ {|@Polynomial|} ⤳ {|@Polynomial|});
symbol {|@poly|} ≔ _poly;
sequential symbol !poly_neg : τ ({|@Polynomial|} ⤳ {|@Polynomial|});
rule !poly_neg {|@poly.zero|} ↪ {|@poly.zero|}
with !poly_neg ({|@poly|} ({|@mon|} ($a) ($c)) ($p)) ↪ eo⋅⋅cons {|@poly|} ({|@mon|} ($a) (eo⋅⋅neg ($c))) (!poly_neg ($p));
sequential symbol !poly_mod_coeffs : τ ({|@Polynomial|} ⤳ Int ⤳ {|@Polynomial|});
rule !poly_mod_coeffs {|@poly.zero|} ($w) ↪ {|@poly.zero|}
with !poly_mod_coeffs ({|@poly|} ({|@mon|} ($a) ($c)) ($p)) ($w) ↪ (let newc ≔ eo⋅⋅zmod (eo⋅⋅to_z ($c)) ($w) in eo⋅⋅ite (eo⋅⋅eq newc (0)) (!poly_mod_coeffs ($p) ($w)) (eo⋅⋅cons {|@poly|} ({|@mon|} ($a) (eo⋅⋅to_q newc)) (!poly_mod_coeffs ($p) ($w))));
sequential symbol !poly_add : τ ({|@Polynomial|} ⤳ {|@Polynomial|} ⤳ {|@Polynomial|});
rule !poly_add ({|@poly|} ({|@mon|} ($a1) ($c1)) ($p1)) ({|@poly|} ({|@mon|} ($a2) ($c2)) ($p2)) ↪ eo⋅⋅ite (eo⋅⋅eq ($a1) ($a2)) ((let ca ≔ eo⋅⋅add ($c1) ($c2) in (let pa ≔ !poly_add ($p1) ($p2) in eo⋅⋅ite (eo⋅⋅eq ca (0/1)) pa (eo⋅⋅cons {|@poly|} ({|@mon|} ($a1) ca) pa)))) (eo⋅⋅ite (!compare_var ($a1) ($a2)) (eo⋅⋅cons {|@poly|} ({|@mon|} ($a1) ($c1)) (!poly_add ($p1) ({|@poly|} ({|@mon|} ($a2) ($c2)) ($p2)))) (eo⋅⋅cons {|@poly|} ({|@mon|} ($a2) ($c2)) (!poly_add ({|@poly|} ({|@mon|} ($a1) ($c1)) ($p1)) ($p2))))
with !poly_add {|@poly.zero|} ($p) ↪ $p
with !poly_add ($p) {|@poly.zero|} ↪ $p;
sequential symbol !mvar_mul_mvar [X : Set] [Y : Set]: τ (X ⤳ Y ⤳ !typeunion X Y);
rule !mvar_mul_mvar (* ($a1) ($a2)) (* ($c1) ($c2)) ↪ eo⋅⋅ite (!compare_var ($a1) ($c1)) (eo⋅⋅cons * ($a1) (!mvar_mul_mvar ($a2) (* ($c1) ($c2)))) (eo⋅⋅cons * ($c1) (!mvar_mul_mvar (* ($a1) ($a2)) ($c2)))
with !mvar_mul_mvar (* ($a1) ($a2)) (1) ↪ * ($a1) ($a2)
with !mvar_mul_mvar (1) (* ($c1) ($c2)) ↪ * ($c1) ($c2)
with !mvar_mul_mvar (bvmul ($ba1) ($ba2)) (bvmul ($bc1) ($bc2)) ↪ eo⋅⋅ite (!compare_var ($ba1) ($bc1)) (eo⋅⋅cons bvmul ($ba1) (!mvar_mul_mvar ($ba2) (bvmul ($bc1) ($bc2)))) (eo⋅⋅cons bvmul ($bc1) (!mvar_mul_mvar (bvmul ($ba1) ($ba2)) ($bc2)))
with !mvar_mul_mvar (bvmul ($ba1) ($ba2)) ($bc1) ↪ eo⋅⋅requires (eo⋅⋅to_z ($bc1)) (1) (bvmul ($ba1) ($ba2))
with !mvar_mul_mvar ($ba1) (bvmul ($bc1) ($bc2)) ↪ eo⋅⋅requires (eo⋅⋅to_z ($ba1)) (1) (bvmul ($bc1) ($bc2))
with !mvar_mul_mvar ($ba1) ($bc1) ↪ eo⋅⋅requires (eo⋅⋅to_z ($ba1)) (1) (eo⋅⋅requires (eo⋅⋅to_z ($bc1)) (1) ($ba1));
sequential symbol !mon_mul_mon : τ ({|@Monomial|} ⤳ {|@Monomial|} ⤳ {|@Monomial|});
rule !mon_mul_mon ({|@mon|} ($a1) ($c1)) ({|@mon|} ($a2) ($c2)) ↪ {|@mon|} (!mvar_mul_mvar ($a1) ($a2)) (eo⋅⋅mul ($c1) ($c2));
sequential symbol !poly_mul_mon : τ ({|@Monomial|} ⤳ {|@Polynomial|} ⤳ {|@Polynomial|});
rule !poly_mul_mon ($m1) ({|@poly|} ($m2) ($p2)) ↪ !poly_add ({|@poly|} (!mon_mul_mon ($m1) ($m2))) (!poly_mul_mon ($m1) ($p2))
with !poly_mul_mon ($m1) {|@poly.zero|} ↪ {|@poly.zero|};
sequential symbol !poly_mul : τ ({|@Polynomial|} ⤳ {|@Polynomial|} ⤳ {|@Polynomial|});
rule !poly_mul ({|@poly|} ($m) ($p1)) ($p) ↪ !poly_add (!poly_mul_mon ($m) ($p)) (!poly_mul ($p1) ($p))
with !poly_mul {|@poly.zero|} ($p) ↪ {|@poly.zero|}
with !poly_mul ($p) {|@poly.zero|} ↪ {|@poly.zero|};
symbol !get_arith_poly_norm_div [U : Set] [V : Set] (a1 : τ U) (a1p : τ {|@Polynomial|}) (a2 : τ V)≔ (let a2q ≔ eo⋅⋅to_q a2 in eo⋅⋅ite (eo⋅⋅ite (eo⋅⋅is_q a2q) (eo⋅⋅not (eo⋅⋅eq a2q (0/1))) false) (!poly_mul_mon ({|@mon|} (1) (eo⋅⋅qdiv (1/1) a2q)) a1p) ({|@poly|} ({|@mon|} (* (/ a1 a2) (1)) (1/1))));
sequential symbol !get_arith_poly_norm [T : Set]: τ (T ⤳ {|@Polynomial|});
rule !get_arith_poly_norm (- ($a1)) ↪ !poly_neg (!get_arith_poly_norm ($a1))
with !get_arith_poly_norm (+ ($a1) ($a2)) ↪ !poly_add (!get_arith_poly_norm ($a1)) (!get_arith_poly_norm ($a2))
with !get_arith_poly_norm (- ($a1) ($a2)) ↪ !poly_add (!get_arith_poly_norm ($a1)) (!poly_neg (!get_arith_poly_norm ($a2)))
with !get_arith_poly_norm (* ($a1) ($a2)) ↪ !poly_mul (!get_arith_poly_norm ($a1)) (!get_arith_poly_norm ($a2))
with !get_arith_poly_norm (/ ($a1) ($a2)) ↪ !get_arith_poly_norm_div ($a1) (!get_arith_poly_norm ($a1)) ($a2)
with !get_arith_poly_norm (/_total ($a1) ($a2)) ↪ !get_arith_poly_norm_div ($a1) (!get_arith_poly_norm ($a1)) ($a2)
with !get_arith_poly_norm (to_real ($a1)) ↪ !get_arith_poly_norm ($a1)
with !get_arith_poly_norm ($a) ↪ (let aq ≔ eo⋅⋅to_q ($a) in eo⋅⋅ite (eo⋅⋅is_q aq) (eo⋅⋅ite (eo⋅⋅is_eq aq (0/1)) {|@poly.zero|} ({|@poly|} ({|@mon|} (1) aq))) ({|@poly|} ({|@mon|} (* ($a) (1)) (1/1))));
sequential symbol !get_bv_poly_norm_rec [m : τ Int]: τ ((BitVec m) ⤳ {|@Polynomial|});
rule !get_bv_poly_norm_rec (bvneg ($b1)) ↪ !poly_neg (!get_bv_poly_norm_rec ($b1))
with !get_bv_poly_norm_rec (bvadd ($b1) ($b2)) ↪ !poly_add (!get_bv_poly_norm_rec ($b1)) (!get_bv_poly_norm_rec ($b2))
with !get_bv_poly_norm_rec (bvsub ($b1) ($b2)) ↪ !poly_add (!get_bv_poly_norm_rec ($b1)) (!poly_neg (!get_bv_poly_norm_rec ($b2)))
with !get_bv_poly_norm_rec (bvmul ($b1) ($b2)) ↪ !poly_mul (!get_bv_poly_norm_rec ($b1)) (!get_bv_poly_norm_rec ($b2))
with !get_bv_poly_norm_rec ($b) ↪ (let bt ≔ eo⋅⋅typeof ($b) in (let one ≔ eo⋅⋅to_bin (!bv_bitwidth bt) (1) in eo⋅⋅ite (eo⋅⋅is_bin ($b)) ((let bz ≔ eo⋅⋅to_z ($b) in eo⋅⋅ite (eo⋅⋅is_eq bz (0)) {|@poly.zero|} ({|@poly|} ({|@mon|} one (eo⋅⋅to_q bz))))) ({|@poly|} ({|@mon|} (bvmul ($b) (eo⋅⋅to_bin m (1))) (1/1)))));
symbol !get_bv_poly_norm [m : τ Int] (w : τ Int) (b : τ (BitVec m))≔ !poly_mod_coeffs (!get_bv_poly_norm_rec b) w;
sequential symbol !arith_poly_to_term_rec : τ ({|@Polynomial|} ⤳ Real);
rule !arith_poly_to_term_rec {|@poly.zero|} ↪ 0/1
with !arith_poly_to_term_rec ({|@poly|} ({|@mon|} ($a) ($c)) ($p)) ↪ + (* ($c) (* ($a) (1))) (+ (!arith_poly_to_term_rec ($p)) (0));
symbol !arith_poly_to_term [T : Set] (t : τ T)≔ !arith_poly_to_term_rec (!get_arith_poly_norm t);
