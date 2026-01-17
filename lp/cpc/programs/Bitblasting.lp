require open cpc.Core Stdlib.Set cpc.programs.BitVectors;
sequential symbol !bv_bitblast_concat [n : τ Int] [m : τ Int]: τ ((BitVec n) ⤳ (BitVec m) ⤳ BitVec (eo⋅⋅add n m));
rule !bv_bitblast_concat ({|@from_bools|} ($x) ($y)) ($z) ↪ eo⋅⋅cons {|@from_bools|} ($x) (!bv_bitblast_concat ($y) ($z))
with !bv_bitblast_concat {|@bv_empty|} ($z) ↪ $z;
sequential symbol !bv_bitblast_binary_app [T : Set]: τ ((T ⤳ T ⤳ Bool) ⤳ Bool ⤳ Bool ⤳ Bool);
rule !bv_bitblast_binary_app and ($a) ($b) ↪ and ($a) ($b)
with !bv_bitblast_binary_app or ($a) ($b) ↪ or ($a) ($b)
with !bv_bitblast_binary_app xor ($a) ($b) ↪ xor ($a) ($b)
with !bv_bitblast_binary_app = ($a) ($b) ↪ and (= ($a) ($b));
sequential symbol !bv_bitblast_repeat [n : τ Int]: τ (Bool ⤳ (eo⋅⋅quote n) ⤳ BitVec n);
rule !bv_bitblast_repeat ($b) (0) ↪ {|@bv_empty|}
with !bv_bitblast_repeat ($b) ($n) ↪ eo⋅⋅cons {|@from_bools|} ($b) (!bv_bitblast_repeat ($b) (eo⋅⋅add ($n) (-1)));
sequential symbol !bv_bitblast_prefix [n : τ Int] [l : τ Int]: τ ((eo⋅⋅quote l) ⤳ (BitVec n) ⤳ BitVec (eo⋅⋅ite (eo⋅⋅gt l n) n l));
rule !bv_bitblast_prefix (0) ($t) ↪ {|@bv_empty|}
with !bv_bitblast_prefix ($l) {|@bv_empty|} ↪ {|@bv_empty|}
with !bv_bitblast_prefix ($l) ({|@from_bools|} ($b) ($a)) ↪ eo⋅⋅cons {|@from_bools|} ($b) (!bv_bitblast_prefix (eo⋅⋅add ($l) (-1)) ($a));
sequential symbol !bv_bitblast_head [n : τ Int]: τ ((BitVec n) ⤳ Bool);
rule !bv_bitblast_head ({|@from_bools|} ($b) ($a)) ↪ $b;
sequential symbol !bv_bitblast_tail [n : τ Int]: τ ((BitVec n) ⤳ BitVec (eo⋅⋅add n (-1)));
rule !bv_bitblast_tail ({|@from_bools|} ($b) ($a)) ↪ $a;
sequential symbol !bv_bitblast_subsequence [n : τ Int] [u : τ Int] [l : τ Int]: τ ((eo⋅⋅quote l) ⤳ (eo⋅⋅quote u) ⤳ (BitVec n) ⤳ BitVec (eo⋅⋅add u (eo⋅⋅neg l)));
rule !bv_bitblast_subsequence ($l) ($u) {|@bv_empty|} ↪ {|@bv_empty|}
with !bv_bitblast_subsequence (0) ($u) ($t) ↪ !bv_bitblast_prefix (eo⋅⋅add ($u) (1)) ($t)
with !bv_bitblast_subsequence ($l) ($u) ({|@from_bools|} ($b) ($a)) ↪ !bv_bitblast_subsequence (eo⋅⋅add ($l) (-1)) (eo⋅⋅add ($u) (-1)) ($a);
symbol !bv_bitblast_zero (n : τ Int)≔ !bv_bitblast_repeat false n;
symbol !bv_bitblast_sign_bit [n : τ Int] (a : τ (BitVec n))≔ !bv_bitblast_head (eo⋅⋅list_rev {|@from_bools|} a);
sequential symbol !bv_bitblast_apply_unary [n : τ Int]: τ ((Bool ⤳ Bool) ⤳ (BitVec n) ⤳ BitVec n);
rule !bv_bitblast_apply_unary ($f) {|@bv_empty|} ↪ {|@bv_empty|}
with !bv_bitblast_apply_unary ($f) ({|@from_bools|} ($b1) ($a1)) ↪ eo⋅⋅cons {|@from_bools|} ($f ($b1)) (!bv_bitblast_apply_unary ($f) ($a1));
sequential symbol !bv_bitblast_apply_binary [T : Set] [n : τ Int]: τ ((T ⤳ T ⤳ Bool) ⤳ (BitVec n) ⤳ (BitVec n) ⤳ BitVec n);
rule !bv_bitblast_apply_binary ($f) {|@bv_empty|} {|@bv_empty|} ↪ {|@bv_empty|}
with !bv_bitblast_apply_binary ($f) ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b2) ($a2)) ↪ eo⋅⋅cons {|@from_bools|} (!bv_bitblast_binary_app ($f) ($b1) ($b2)) (!bv_bitblast_apply_binary ($f) ($a1) ($a2));
sequential symbol !bv_bitblast_apply_ite [n : τ Int]: τ (Bool ⤳ (BitVec n) ⤳ (BitVec n) ⤳ BitVec n);
rule !bv_bitblast_apply_ite ($bc) {|@bv_empty|} {|@bv_empty|} ↪ {|@bv_empty|}
with !bv_bitblast_apply_ite ($bc) ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b2) ($a2)) ↪ eo⋅⋅cons {|@from_bools|} (ite ($bc) ($b1) ($b2)) (!bv_bitblast_apply_ite ($bc) ($a1) ($a2));
symbol !bv_bitblast_rshift [n : τ Int] (a : τ (BitVec n)) (amount : τ Int)≔ (let len ≔ eo⋅⋅list_len {|@from_bools|} a in !bv_bitblast_concat (!bv_bitblast_subsequence amount len a) (!bv_bitblast_repeat false amount));
symbol !bv_bitblast_lshift [n : τ Int] (a : τ (BitVec n)) (amount : τ Int)≔ (let len ≔ eo⋅⋅list_len {|@from_bools|} a in !bv_bitblast_concat (!bv_bitblast_repeat false amount) (!bv_bitblast_subsequence (0) (eo⋅⋅add len (eo⋅⋅neg amount) (-1)) a));
sequential symbol !bv_mk_bitblast_step_eq_rec [n : τ Int]: τ ((BitVec n) ⤳ (BitVec n) ⤳ Bool);
rule !bv_mk_bitblast_step_eq_rec {|@bv_empty|} {|@bv_empty|} ↪ true
with !bv_mk_bitblast_step_eq_rec ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b2) ($a2)) ↪ eo⋅⋅cons and (and (= ($b1) ($b2))) (!bv_mk_bitblast_step_eq_rec ($a1) ($a2));
symbol !bv_mk_bitblast_step_eq [n : τ Int] (a1 : τ (BitVec n)) (a2 : τ (BitVec n))≔ eo⋅⋅list_singleton_elim and (!bv_mk_bitblast_step_eq_rec a1 a2);
sequential symbol !bv_bitblast_ult_rec [n : τ Int]: τ ((BitVec n) ⤳ (BitVec n) ⤳ Bool ⤳ Bool);
rule !bv_bitblast_ult_rec {|@bv_empty|} {|@bv_empty|} ($res) ↪ $res
with !bv_bitblast_ult_rec ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b2) ($a2)) ($res) ↪ !bv_bitblast_ult_rec ($a1) ($a2) (or (and (and (= ($b1) ($b2))) ($res)) (and (not ($b1)) ($b2)));
sequential symbol !bv_bitblast_ult [n : τ Int]: τ ((BitVec n) ⤳ (BitVec n) ⤳ Bool ⤳ Bool);
rule !bv_bitblast_ult ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b2) ($a2)) ($orEqual) ↪ (let res ≔ and (not ($b1)) ($b2) in (let res2 ≔ eo⋅⋅ite ($orEqual) (or res (and (= ($b1) ($b2)))) res in !bv_bitblast_ult_rec ($a1) ($a2) res));
sequential symbol !bv_bitblast_slt_impl [n : τ Int]: τ ((BitVec n) ⤳ (BitVec n) ⤳ Bool ⤳ Bool);
rule !bv_bitblast_slt_impl ({|@from_bools|} ($b1) {|@bv_empty|}) ({|@from_bools|} ($b2) {|@bv_empty|}) ($orEqual) ↪ eo⋅⋅ite ($orEqual) (or (and (= ($b1) ($b2))) (and ($b1) (not ($b2)))) (and ($b1) (not ($b2)))
with !bv_bitblast_slt_impl ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b2) ($a2)) ($orEqual) ↪ (let ures ≔ !bv_bitblast_ult (eo⋅⋅list_rev {|@from_bools|} ($a1)) (eo⋅⋅list_rev {|@from_bools|} ($a2)) ($orEqual) in or (and (and (= ($b1) ($b2))) ures) (and ($b1) (not ($b2))));
symbol !bv_bitblast_slt [n : τ Int] (x : τ (BitVec n)) (y : τ (BitVec n)) (orEqual : τ Bool)≔ !bv_bitblast_slt_impl (eo⋅⋅list_rev {|@from_bools|} x) (eo⋅⋅list_rev {|@from_bools|} y) orEqual;
symbol !bv_mk_bitblast_step_extract [n : τ Int] (u : τ Int) (l : τ Int) (a : τ (BitVec n))≔ !bv_bitblast_subsequence l u a;
sequential symbol !bv_mk_bitblast_step_concat [n : τ Int]: τ ((BitVec n) ⤳ BitVec n);
rule !bv_mk_bitblast_step_concat {|@bv_empty|} ↪ {|@bv_empty|}
with !bv_mk_bitblast_step_concat (concat ($a1) ($a2)) ↪ !bv_bitblast_concat (!bv_mk_bitblast_step_concat ($a2)) ($a1);
sequential symbol !bv_mk_bitblast_step_bitwise [T : Set] [n : τ Int] [m : τ Int]: τ (((BitVec n) ⤳ (BitVec n) ⤳ BitVec n) ⤳ (T ⤳ T ⤳ Bool) ⤳ (BitVec m) ⤳ (BitVec m) ⤳ BitVec m);
rule !bv_mk_bitblast_step_bitwise ($bf) ($f) ($bf ($a1) ($a2)) ($ac) ↪ !bv_mk_bitblast_step_bitwise ($bf) ($f) ($a2) (!bv_bitblast_apply_binary ($f) ($ac) ($a1))
with !bv_mk_bitblast_step_bitwise ($bf) ($f) ($a2) ($ac) ↪ $ac;
sequential symbol !bv_ripple_carry_adder_2 [n : τ Int] [m : τ Int]: τ ((BitVec n) ⤳ (BitVec n) ⤳ Bool ⤳ (BitVec m) ⤳ {|@Pair|} Bool (BitVec (eo⋅⋅add n m)));
rule !bv_ripple_carry_adder_2 ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b2) ($a2)) ($carry) ($res) ↪ !bv_ripple_carry_adder_2 ($a1) ($a2) (or (and ($b1) ($b2)) (and (xor ($b1) ($b2)) ($carry))) (eo⋅⋅cons {|@from_bools|} (xor (xor ($b1) ($b2)) ($carry)) ($res))
with !bv_ripple_carry_adder_2 {|@bv_empty|} {|@bv_empty|} ($carry) ($res) ↪ {|@pair|} ($carry) (eo⋅⋅list_rev {|@from_bools|} ($res));
symbol !bv_ripple_carry_adder [n : τ Int] (a1 : τ (BitVec n)) (a2 : τ (BitVec n)) (carry : τ Bool)≔ !pair_second (!bv_ripple_carry_adder_2 a1 a2 carry {|@bv_empty|});
sequential symbol !bv_mk_bitblast_step_add [n : τ Int]: τ ((BitVec n) ⤳ (BitVec n) ⤳ BitVec n);
rule !bv_mk_bitblast_step_add (bvadd ($a1) ($a2)) ($ac) ↪ !bv_mk_bitblast_step_add ($a2) (!bv_ripple_carry_adder ($ac) ($a1) false)
with !bv_mk_bitblast_step_add ($a2) ($ac) ↪ $ac;
sequential symbol !bv_shift_add_multiplier_rec_step [n : τ Int] [np : τ Int]: τ (Bool ⤳ (BitVec n) ⤳ Int ⤳ (BitVec np) ⤳ Bool ⤳ BitVec np);
rule !bv_shift_add_multiplier_rec_step ($b1) ($a2) (0) {|@bv_empty|} ($carry) ↪ {|@bv_empty|}
with !bv_shift_add_multiplier_rec_step ($b1) ({|@from_bools|} ($b2) ($a2)) (0) ({|@from_bools|} ($br) ($ar)) ($carry) ↪ (let aj ≔ and ($b1) ($b2) in eo⋅⋅cons {|@from_bools|} (xor (xor ($br) aj) ($carry)) (!bv_shift_add_multiplier_rec_step ($b1) ($a2) (0) ($ar) (or (and ($br) aj) (and (xor ($br) aj) ($carry)))))
with !bv_shift_add_multiplier_rec_step ($b1) ($a2) ($k) ({|@from_bools|} ($br) ($ar)) ($carry) ↪ eo⋅⋅cons {|@from_bools|} ($br) (!bv_shift_add_multiplier_rec_step ($b1) ($a2) (eo⋅⋅add ($k) (-1)) ($ar) ($carry));
sequential symbol !bv_shift_add_multiplier_rec [n : τ Int] [m : τ Int]: τ ((BitVec m) ⤳ (BitVec n) ⤳ Int ⤳ (BitVec n) ⤳ BitVec n);
rule !bv_shift_add_multiplier_rec {|@bv_empty|} ($a2) ($k) ($res) ↪ $res
with !bv_shift_add_multiplier_rec ({|@from_bools|} ($b1) ($a1)) ($a2) ($k) ($res) ↪ !bv_shift_add_multiplier_rec ($a1) ($a2) (eo⋅⋅add ($k) (1)) (!bv_shift_add_multiplier_rec_step ($b1) ($a2) ($k) ($res) false);
sequential symbol !bv_shift_add_multiplier [n : τ Int] [m : τ Int]: τ ((BitVec n) ⤳ (BitVec m) ⤳ BitVec n);
rule !bv_shift_add_multiplier ($a2) ({|@from_bools|} ($b1) ($a1)) ↪ (let sz ≔ !bv_bitwidth (eo⋅⋅typeof ($a2)) in !bv_shift_add_multiplier_rec ($a1) ($a2) (1) (!bv_bitblast_apply_binary and (!bv_bitblast_repeat ($b1) sz) ($a2)));
sequential symbol !bv_mk_bitblast_step_mul [n : τ Int]: τ ((BitVec n) ⤳ (BitVec n) ⤳ BitVec n);
rule !bv_mk_bitblast_step_mul (bvmul ($a1) ($a2)) ($ac) ↪ !bv_mk_bitblast_step_mul ($a2) (!bv_shift_add_multiplier ($ac) ($a1))
with !bv_mk_bitblast_step_mul ($a2) ($ac) ↪ $ac;
sequential symbol !bv_div_mod_impl [n : τ Int]: τ ((BitVec n) ⤳ (BitVec n) ⤳ (BitVec n) ⤳ Int ⤳ {|@Pair|} (BitVec n) (BitVec n));
rule !bv_div_mod_impl ($a1) ($a2) ($zero) (0) ↪ {|@pair|} ($zero) ($zero)
with !bv_div_mod_impl ($zero) ($a2) ($zero) ($sz) ↪ {|@pair|} ($zero) ($zero)
with !bv_div_mod_impl ($a1) ($a2) ($zero) ($sz) ↪ (let recres ≔ !bv_div_mod_impl (!bv_bitblast_rshift ($a1) (1)) ($a2) ($zero) (eo⋅⋅add ($sz) (-1)) in (let isodd ≔ !bv_bitblast_head ($a1) in (let q1s ≔ !bv_bitblast_lshift (!pair_first recres) (1) in (let r1s ≔ !bv_bitblast_lshift (!pair_second recres) (1) in (let r1sa ≔ !bv_ripple_carry_adder r1s ($zero) (ite (and (= isodd true)) true false) in (let a2n ≔ !bv_bitblast_apply_unary not ($a2) in (let cares1 ≔ !bv_ripple_carry_adder_2 r1sa a2n true {|@bv_empty|} in (let rmb_carry ≔ !pair_first cares1 in (let rmb ≔ !pair_second cares1 in (let q1ss ≔ eo⋅⋅cons {|@from_bools|} (ite (not rmb_carry) (!bv_bitblast_head q1s) true) (!bv_bitblast_tail q1s) in (let r1sa2 ≔ !bv_bitblast_apply_ite (not rmb_carry) r1sa rmb in (let cares2 ≔ !bv_ripple_carry_adder_2 ($a1) a2n true {|@bv_empty|} in (let amb_carry ≔ !pair_first cares2 in {|@pair|} (!bv_bitblast_apply_ite (not amb_carry) ($zero) q1ss) (!bv_bitblast_apply_ite (not amb_carry) ($a1) r1sa2))))))))))))));
symbol !bv_mk_bitblast_step_udiv [n : τ Int] (a1 : τ (BitVec n)) (a2 : τ (BitVec n))≔ (let sz ≔ !bv_bitwidth (eo⋅⋅typeof a1) in (let zero ≔ !bv_bitblast_zero sz in (let res ≔ !bv_div_mod_impl a1 a2 zero sz in (let isz ≔ !bv_mk_bitblast_step_eq a2 zero in !bv_bitblast_apply_ite isz (!bv_bitblast_repeat true sz) (!pair_first res)))));
symbol !bv_mk_bitblast_step_urem [n : τ Int] (a1 : τ (BitVec n)) (a2 : τ (BitVec n))≔ (let sz ≔ !bv_bitwidth (eo⋅⋅typeof a1) in (let zero ≔ !bv_bitblast_zero sz in (let res ≔ !bv_div_mod_impl a1 a2 zero sz in (let isz ≔ !bv_mk_bitblast_step_eq a2 zero in !bv_bitblast_apply_ite isz a1 (!pair_second res)))));
sequential symbol !bv_mk_bitblast_step_ite [n : τ Int]: τ ((BitVec (1)) ⤳ (BitVec n) ⤳ (BitVec n) ⤳ BitVec n);
rule !bv_mk_bitblast_step_ite ({|@from_bools|} ($bc) {|@bv_empty|}) ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b2) ($a2)) ↪ eo⋅⋅cons {|@from_bools|} (and (or (not ($bc)) ($b1)) (or ($bc) ($b2))) (!bv_mk_bitblast_step_ite ({|@from_bools|} ($bc) {|@bv_empty|}) ($a1) ($a2))
with !bv_mk_bitblast_step_ite ({|@from_bools|} ($bc) {|@bv_empty|}) {|@bv_empty|} {|@bv_empty|} ↪ {|@bv_empty|};
sequential symbol !bv_const_to_bitlist_rec [n : τ Int] [i : τ Int]: τ ((BitVec n) ⤳ (eo⋅⋅quote i) ⤳ Int ⤳ BitVec (eo⋅⋅add n (eo⋅⋅neg i)));
rule !bv_const_to_bitlist_rec ($c) ($n) ($n) ↪ {|@bv_empty|}
with !bv_const_to_bitlist_rec ($c) ($i) ($n) ↪ eo⋅⋅cons {|@from_bools|} (!bv_bit_set ($c) ($i)) (!bv_const_to_bitlist_rec ($c) (eo⋅⋅add ($i) (1)) ($n));
symbol !bv_mk_bitblast_step_const [n : τ Int] (a : τ (BitVec n))≔ !bv_const_to_bitlist_rec a (0) (eo⋅⋅len a);
sequential symbol !bv_mk_bitblast_step_shl_rec_step [n : τ Int] [m : τ Int]: τ ((BitVec m) ⤳ (BitVec n) ⤳ Int ⤳ Bool ⤳ BitVec m);
rule !bv_mk_bitblast_step_shl_rec_step {|@bv_empty|} ($a1c) ($i) ($b2) ↪ {|@bv_empty|}
with !bv_mk_bitblast_step_shl_rec_step ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b1c) ($a1c)) (0) ($b2) ↪ eo⋅⋅cons {|@from_bools|} (ite ($b2) ($b1c) ($b1)) (!bv_mk_bitblast_step_shl_rec_step ($a1) ($a1c) (0) ($b2))
with !bv_mk_bitblast_step_shl_rec_step ({|@from_bools|} ($b1) ($a1)) ($a1c) ($i) ($b2) ↪ eo⋅⋅cons {|@from_bools|} (ite ($b2) false ($b1)) (!bv_mk_bitblast_step_shl_rec_step ($a1) ($a1c) (eo⋅⋅add ($i) (-1)) ($b2));
sequential symbol !bv_mk_bitblast_step_shl_rec [n : τ Int] [m : τ Int]: τ ((BitVec n) ⤳ (BitVec m) ⤳ Int ⤳ Int ⤳ BitVec n);
rule !bv_mk_bitblast_step_shl_rec ($a1) ($a2) ($lsz) ($lsz) ↪ $a1
with !bv_mk_bitblast_step_shl_rec ($a1) ({|@from_bools|} ($b2) ($a2)) ($s) ($lsz) ↪ !bv_mk_bitblast_step_shl_rec (!bv_mk_bitblast_step_shl_rec_step ($a1) ($a1) (!arith_eval_int_pow_2 ($s)) ($b2)) ($a2) (eo⋅⋅add ($s) (1)) ($lsz);
symbol !bv_mk_bitblast_step_shl [n : τ Int] (a1 : τ (BitVec n)) (a2 : τ (BitVec n))≔ (let sz ≔ !bv_bitwidth (eo⋅⋅typeof a1) in (let lsz1 ≔ !arith_eval_int_log_2 sz in (let lsz ≔ eo⋅⋅ite (!arith_eval_int_is_pow_2 sz) lsz1 (eo⋅⋅add lsz1 (1)) in (let res ≔ !bv_mk_bitblast_step_shl_rec a1 a2 (0) lsz in (let szc ≔ !bv_mk_bitblast_step_const (eo⋅⋅to_bin sz sz) in !bv_bitblast_apply_ite (!bv_bitblast_ult a2 szc false) res (!bv_bitblast_repeat false sz))))));
sequential symbol !bv_mk_bitblast_step_shr_rec_step [n : τ Int] [m : τ Int]: τ ((BitVec m) ⤳ (BitVec n) ⤳ Int ⤳ Bool ⤳ Bool ⤳ BitVec m);
rule !bv_mk_bitblast_step_shr_rec_step {|@bv_empty|} ($a1c) ($i) ($b2) ($sbit) ↪ {|@bv_empty|}
with !bv_mk_bitblast_step_shr_rec_step ({|@from_bools|} ($b1) ($a1)) ({|@from_bools|} ($b1c) ($a1c)) (0) ($b2) ($sbit) ↪ eo⋅⋅cons {|@from_bools|} (ite (not ($b2)) ($b1) ($b1c)) (!bv_mk_bitblast_step_shr_rec_step ($a1) ($a1c) (0) ($b2) ($sbit))
with !bv_mk_bitblast_step_shr_rec_step ({|@from_bools|} ($b1) ($a1)) {|@bv_empty|} (0) ($b2) ($sbit) ↪ eo⋅⋅cons {|@from_bools|} (ite ($b2) ($sbit) ($b1)) (!bv_mk_bitblast_step_shr_rec_step ($a1) {|@bv_empty|} (0) ($b2) ($sbit))
with !bv_mk_bitblast_step_shr_rec_step ($a1) ({|@from_bools|} ($b1c) ($a1c)) ($i) ($b2) ($sbit) ↪ !bv_mk_bitblast_step_shr_rec_step ($a1) ($a1c) (eo⋅⋅add ($i) (-1)) ($b2) ($sbit);
sequential symbol !bv_mk_bitblast_step_shr_rec [n : τ Int] [m : τ Int]: τ ((BitVec n) ⤳ (BitVec m) ⤳ Int ⤳ Int ⤳ Bool ⤳ BitVec n);
rule !bv_mk_bitblast_step_shr_rec ($a1) ($a2) ($lsz) ($lsz) ($sbit) ↪ $a1
with !bv_mk_bitblast_step_shr_rec ($a1) ({|@from_bools|} ($b2) ($a2)) ($s) ($lsz) ($sbit) ↪ !bv_mk_bitblast_step_shr_rec (!bv_mk_bitblast_step_shr_rec_step ($a1) ($a1) (!arith_eval_int_pow_2 ($s)) ($b2) ($sbit)) ($a2) (eo⋅⋅add ($s) (1)) ($lsz) ($sbit);
symbol !bv_mk_bitblast_step_shr [n : τ Int] (a1 : τ (BitVec n)) (a2 : τ (BitVec n)) (sbit : τ Bool)≔ (let sz ≔ !bv_bitwidth (eo⋅⋅typeof a1) in (let lsz1 ≔ !arith_eval_int_log_2 sz in (let lsz ≔ eo⋅⋅ite (!arith_eval_int_is_pow_2 sz) lsz1 (eo⋅⋅add lsz1 (1)) in (let res ≔ !bv_mk_bitblast_step_shr_rec a1 a2 (0) lsz sbit in (let szc ≔ !bv_mk_bitblast_step_const (eo⋅⋅to_bin sz sz) in !bv_bitblast_apply_ite (!bv_bitblast_ult a2 szc false) res (!bv_bitblast_repeat sbit sz))))));
sequential symbol !bv_mk_bitblast_step_var_rec [n : τ Int] [i : τ Int]: τ ((BitVec n) ⤳ (eo⋅⋅quote i) ⤳ BitVec (eo⋅⋅add i (1)));
rule !bv_mk_bitblast_step_var_rec ($a) (-1) ↪ {|@bv_empty|}
with !bv_mk_bitblast_step_var_rec ($a) ($i) ↪ eo⋅⋅cons {|@from_bools|} ({|@bit|} ($i) ($a)) (!bv_mk_bitblast_step_var_rec ($a) (eo⋅⋅add ($i) (-1)));
symbol !bv_mk_bitblast_step_var [n : τ Int] (a : τ (BitVec n))≔ eo⋅⋅list_rev {|@from_bools|} (!bv_mk_bitblast_step_var_rec a (eo⋅⋅add (!bv_bitwidth (eo⋅⋅typeof a)) (-1)));
sequential symbol !bv_mk_bitblast_step [T : Set]: τ (T ⤳ T);
rule !bv_mk_bitblast_step (bvnot ($a1)) ↪ !bv_bitblast_apply_unary not ($a1)
with !bv_mk_bitblast_step (and (= ($a1) ($a2))) ↪ !bv_mk_bitblast_step_eq ($a1) ($a2)
with !bv_mk_bitblast_step (and (bvult ($a1) ($a2))) ↪ !bv_bitblast_ult ($a1) ($a2) false
with !bv_mk_bitblast_step (bvule ($a1) ($a2)) ↪ !bv_bitblast_ult ($a1) ($a2) true
with !bv_mk_bitblast_step (bvslt ($a1) ($a2)) ↪ !bv_bitblast_slt ($a1) ($a2) false
with !bv_mk_bitblast_step (bvsle ($a1) ($a2)) ↪ !bv_bitblast_slt ($a1) ($a2) true
with !bv_mk_bitblast_step (extract ($u) ($l) ($a1)) ↪ !bv_mk_bitblast_step_extract ($u) ($l) ($a1)
with !bv_mk_bitblast_step (concat ($a1) ($a3)) ↪ !bv_mk_bitblast_step_concat (concat ($a1) ($a3))
with !bv_mk_bitblast_step (bvor ($a1) ($a2)) ↪ !bv_mk_bitblast_step_bitwise bvor or ($a2) ($a1)
with !bv_mk_bitblast_step (bvand ($a1) ($a2)) ↪ !bv_mk_bitblast_step_bitwise bvand and ($a2) ($a1)
with !bv_mk_bitblast_step (bvxor ($a1) ($a2)) ↪ !bv_mk_bitblast_step_bitwise bvxor xor ($a2) ($a1)
with !bv_mk_bitblast_step (bvxnor ($a1) ($a2)) ↪ !bv_bitblast_apply_binary = ($a1) ($a2)
with !bv_mk_bitblast_step (bvadd ($a1) ($a2)) ↪ !bv_mk_bitblast_step_add ($a2) ($a1)
with !bv_mk_bitblast_step (bvmul ($a1) ($a2)) ↪ !bv_mk_bitblast_step_mul ($a2) ($a1)
with !bv_mk_bitblast_step (bvudiv ($a1) ($a2)) ↪ !bv_mk_bitblast_step_udiv ($a1) ($a2)
with !bv_mk_bitblast_step (bvurem ($a1) ($a2)) ↪ !bv_mk_bitblast_step_urem ($a1) ($a2)
with !bv_mk_bitblast_step (bvsub ($a1) ($a2)) ↪ !bv_ripple_carry_adder ($a1) (!bv_bitblast_apply_unary not ($a2)) true
with !bv_mk_bitblast_step (bvneg ($a1)) ↪ !bv_ripple_carry_adder (!bv_bitblast_apply_unary not ($a1)) (!bv_bitblast_zero (!bv_bitwidth (eo⋅⋅typeof ($a1)))) true
with !bv_mk_bitblast_step (bvite ($ac) ($a1) ($a2)) ↪ !bv_mk_bitblast_step_ite ($ac) ($a1) ($a2)
with !bv_mk_bitblast_step (bvashr ($a1) ($a2)) ↪ !bv_mk_bitblast_step_shr ($a1) ($a2) (!bv_bitblast_sign_bit ($a1))
with !bv_mk_bitblast_step (bvlshr ($a1) ($a2)) ↪ !bv_mk_bitblast_step_shr ($a1) ($a2) false
with !bv_mk_bitblast_step (bvshl ($a1) ($a2)) ↪ !bv_mk_bitblast_step_shl ($a1) ($a2)
with !bv_mk_bitblast_step (bvcomp ($a1) ($a2)) ↪ {|@from_bools|} (!bv_mk_bitblast_step_eq ($a1) ($a2)) {|@bv_empty|}
with !bv_mk_bitblast_step (bvultbv ($a1) ($a2)) ↪ {|@from_bools|} (!bv_bitblast_ult ($a1) ($a2) false) {|@bv_empty|}
with !bv_mk_bitblast_step (bvsltbv ($a1) ($a2)) ↪ {|@from_bools|} (!bv_bitblast_slt ($a1) ($a2) false) {|@bv_empty|}
with !bv_mk_bitblast_step (sign_extend ($n) ($a1)) ↪ !bv_bitblast_concat ($a1) (!bv_bitblast_repeat (!bv_bitblast_sign_bit ($a1)) ($n))
with !bv_mk_bitblast_step ($a1) ↪ eo⋅⋅ite (eo⋅⋅is_bin ($a1)) (!bv_mk_bitblast_step_const ($a1)) (!bv_mk_bitblast_step_var ($a1));
