require open cpc.Core Stdlib.Set cpc.rules.Builtin cpc.rules.Booleans cpc.rules.Arrays cpc.rules.Uf cpc.rules.Arith cpc.rules.BitVectors cpc.rules.Strings cpc.rules.Sets cpc.rules.ArithBvConv cpc.rules.Quantifiers cpc.rules.Datatypes cpc.rules.Rewrites cpc.programs.DistinctValues cpc.programs.AciNorm;
constant symbol {|@const|} (id : τ Int) (T : Set): τ T;
symbol {|@var|} (s : τ String) (T : Set)≔ eo⋅⋅var s T;
sequential symbol !run_evaluate [S : Set]: τ (S ⤳ S);
rule !run_evaluate (and (= ($x) ($y))) ↪ (let ex ≔ !run_evaluate ($x) in (let ey ≔ !run_evaluate ($y) in (let res ≔ eo⋅⋅eq ex ey in eo⋅⋅ite (eo⋅⋅and (eo⋅⋅is_q ex) (eo⋅⋅is_q ey)) res (eo⋅⋅ite (eo⋅⋅and (eo⋅⋅is_z ex) (eo⋅⋅is_z ey)) res (eo⋅⋅ite (eo⋅⋅and (eo⋅⋅is_bin ex) (eo⋅⋅is_bin ey)) res (eo⋅⋅ite (eo⋅⋅and (eo⋅⋅is_str ex) (eo⋅⋅is_str ey)) res (eo⋅⋅ite (eo⋅⋅and (eo⋅⋅is_bool ex) (eo⋅⋅is_bool ey)) res (and (= ex ey)))))))))
with !run_evaluate (not ($b)) ↪ eo⋅⋅not (!run_evaluate ($b))
with !run_evaluate (ite ($b) ($x) ($y)) ↪ eo⋅⋅ite (!run_evaluate ($b)) (!run_evaluate ($x)) (!run_evaluate ($y))
with !run_evaluate (or ($b) ($bs)) ↪ eo⋅⋅or (!run_evaluate ($b)) (!run_evaluate ($bs))
with !run_evaluate (=> ($b) ($b2)) ↪ eo⋅⋅or (eo⋅⋅not (!run_evaluate ($b))) (!run_evaluate ($b2))
with !run_evaluate (and ($b) ($bs)) ↪ eo⋅⋅and (!run_evaluate ($b)) (!run_evaluate ($bs))
with !run_evaluate (xor ($b) ($b2)) ↪ eo⋅⋅xor (!run_evaluate ($b)) (!run_evaluate ($b2))
with !run_evaluate (and (< ($x) ($z))) ↪ eo⋅⋅is_neg (!arith_eval_qsub (!run_evaluate ($x)) (!run_evaluate ($z)))
with !run_evaluate (and (<= ($x) ($z))) ↪ (let d ≔ !arith_eval_qsub (!run_evaluate ($x)) (!run_evaluate ($z)) in eo⋅⋅or (eo⋅⋅is_neg d) (eo⋅⋅eq d (0/1)))
with !run_evaluate (and (> ($x) ($z))) ↪ eo⋅⋅is_neg (!arith_eval_qsub (!run_evaluate ($z)) (!run_evaluate ($x)))
with !run_evaluate (and (>= ($x) ($z))) ↪ (let d ≔ !arith_eval_qsub (!run_evaluate ($z)) (!run_evaluate ($x)) in eo⋅⋅or (eo⋅⋅is_neg d) (eo⋅⋅eq d (0/1)))
with !run_evaluate (+ ($x) ($ys)) ↪ !arith_eval_add (!run_evaluate ($x)) (!run_evaluate ($ys))
with !run_evaluate (- ($x) ($z)) ↪ !arith_eval_sub (!run_evaluate ($x)) (!run_evaluate ($z))
with !run_evaluate (* ($x) ($ys)) ↪ !arith_eval_mul (!run_evaluate ($x)) (!run_evaluate ($ys))
with !run_evaluate (- ($x)) ↪ eo⋅⋅neg (!run_evaluate ($x))
with !run_evaluate (/ ($x) ($y)) ↪ eo⋅⋅qdiv (eo⋅⋅to_q (!run_evaluate ($x))) (eo⋅⋅to_q (!run_evaluate ($y)))
with !run_evaluate (/_total ($x) ($y)) ↪ (let d ≔ eo⋅⋅to_q (!run_evaluate ($y)) in eo⋅⋅ite (eo⋅⋅eq d (0/1)) (0/1) (eo⋅⋅qdiv (eo⋅⋅to_q (!run_evaluate ($x))) d))
with !run_evaluate (div ($i1) ($i2)) ↪ eo⋅⋅zdiv (!run_evaluate ($i1)) (!run_evaluate ($i2))
with !run_evaluate (div_total ($i1) ($i2)) ↪ (let d ≔ !run_evaluate ($i2) in eo⋅⋅ite (eo⋅⋅eq d (0)) (0) (eo⋅⋅zdiv (!run_evaluate ($i1)) d))
with !run_evaluate (mod ($i1) ($i2)) ↪ eo⋅⋅zmod (!run_evaluate ($i1)) (!run_evaluate ($i2))
with !run_evaluate (mod_total ($i1) ($i2)) ↪ (let ex ≔ !run_evaluate ($i1) in (let ey ≔ !run_evaluate ($i2) in eo⋅⋅ite (eo⋅⋅eq ey (0)) ex (eo⋅⋅zmod ex ey)))
with !run_evaluate (to_real ($x)) ↪ eo⋅⋅to_q (!run_evaluate ($x))
with !run_evaluate (to_int ($x)) ↪ eo⋅⋅to_z (!run_evaluate ($x))
with !run_evaluate (is_int ($x)) ↪ (let ex ≔ !run_evaluate ($x) in eo⋅⋅eq (eo⋅⋅to_q (eo⋅⋅to_z ex)) (eo⋅⋅to_q ex))
with !run_evaluate (abs ($x)) ↪ (let ex ≔ !run_evaluate ($x) in eo⋅⋅ite (eo⋅⋅is_neg ex) (eo⋅⋅neg ex) ex)
with !run_evaluate (int⋅log2 ($i1)) ↪ !arith_eval_int_log_2 (!run_evaluate ($i1))
with !run_evaluate (int⋅pow2 ($i1)) ↪ !arith_eval_int_pow_2 (!run_evaluate ($i1))
with !run_evaluate (int⋅ispow2 ($i1)) ↪ !arith_eval_int_is_pow_2 (!run_evaluate ($i1))
with !run_evaluate (str⋅++ ($sx) ($sys)) ↪ eo⋅⋅concat (!run_evaluate ($sx)) (!run_evaluate ($sys))
with !run_evaluate (str⋅len ($sx)) ↪ eo⋅⋅len (!run_evaluate ($sx))
with !run_evaluate (str⋅substr ($sx) ($n) ($m)) ↪ (let r ≔ !run_evaluate ($n) in eo⋅⋅extract (!run_evaluate ($sx)) r (eo⋅⋅add r (!run_evaluate ($m)) (-1)))
with !run_evaluate (str⋅at ($sx) ($n)) ↪ (let r ≔ !run_evaluate ($n) in eo⋅⋅extract (!run_evaluate ($sx)) r r)
with !run_evaluate (str⋅contains ($sx) ($sy)) ↪ eo⋅⋅not (eo⋅⋅is_neg (eo⋅⋅find (!run_evaluate ($sx)) (!run_evaluate ($sy))))
with !run_evaluate (str⋅replace ($sx) ($sy) ($sz)) ↪ (let ex ≔ !run_evaluate ($sx) in (let ey ≔ !run_evaluate ($sy) in (let r ≔ eo⋅⋅find (eo⋅⋅to_str ex) (eo⋅⋅to_str ey) in eo⋅⋅ite (eo⋅⋅is_neg r) ex (eo⋅⋅concat (eo⋅⋅extract ex (0) (eo⋅⋅add r (-1))) (!run_evaluate ($sz)) (eo⋅⋅extract ex (eo⋅⋅add r (eo⋅⋅len ey)) (eo⋅⋅len ex))))))
with !run_evaluate (str⋅replace_all ($ssx) ($ssy) ($ssz)) ↪ !str_eval_replace_all ($ssx) ($ssy) ($ssz)
with !run_evaluate (str⋅prefixof ($sx) ($sy)) ↪ (let ex ≔ !run_evaluate ($sx) in (let ey ≔ !run_evaluate ($sy) in (let r ≔ eo⋅⋅extract ey (0) (eo⋅⋅add (eo⋅⋅len ex) (-1)) in eo⋅⋅eq ex r)))
with !run_evaluate (str⋅suffixof ($sx) ($sy)) ↪ (let ex ≔ !run_evaluate ($sx) in (let ey ≔ !run_evaluate ($sy) in (let eyl ≔ eo⋅⋅len ey in (let r ≔ eo⋅⋅extract ey (eo⋅⋅add eyl (eo⋅⋅neg (eo⋅⋅len ex))) (eo⋅⋅add eyl (-1)) in eo⋅⋅eq ex r))))
with !run_evaluate (str⋅indexof ($sx) ($sy) ($n)) ↪ (let en ≔ !run_evaluate ($n) in eo⋅⋅ite (eo⋅⋅is_neg en) (-1) ((let ex ≔ !run_evaluate ($sx) in (let exl ≔ eo⋅⋅len ex in eo⋅⋅ite (eo⋅⋅gt en exl) (-1) ((let exs ≔ eo⋅⋅extract ex ($n) exl in (let ey ≔ !run_evaluate ($sy) in (let r ≔ eo⋅⋅find (eo⋅⋅to_str exs) (eo⋅⋅to_str ey) in eo⋅⋅ite (eo⋅⋅is_neg r) r (eo⋅⋅add ($n) r)))))))))
with !run_evaluate (str⋅to_code ($ssx)) ↪ (let ex ≔ !run_evaluate ($ssx) in (let len ≔ eo⋅⋅len ex in eo⋅⋅ite (eo⋅⋅eq len (1)) (eo⋅⋅to_z ex) (eo⋅⋅ite (eo⋅⋅is_z len) (-1) (str⋅to_code ex))))
with !run_evaluate (str⋅from_code ($n)) ↪ (let ex ≔ !run_evaluate ($n) in eo⋅⋅ite (!str_is_code_point ex) (eo⋅⋅to_str ($n)) (""))
with !run_evaluate (str⋅to_int ($ssx)) ↪ (let ex ≔ !run_evaluate ($ssx) in !str_to_int_eval ex)
with !run_evaluate (str⋅from_int ($n)) ↪ (let en ≔ !run_evaluate ($n) in !str_from_int_eval en)
with !run_evaluate (str⋅<= ($ssx) ($ssy)) ↪ (let ex ≔ !run_evaluate ($ssx) in (let ey ≔ !run_evaluate ($ssy) in !str_leq_eval ex ey))
with !run_evaluate (str⋅to_lower ($ssx)) ↪ (let ex ≔ !run_evaluate ($ssx) in !str_to_lower_eval ex)
with !run_evaluate (str⋅to_upper ($ssx)) ↪ (let ex ≔ !run_evaluate ($ssx) in !str_to_upper_eval ex)
with !run_evaluate (str⋅rev ($sx)) ↪ (let ex ≔ !run_evaluate ($sx) in !str_rev_eval ex)
with !run_evaluate (str⋅update ($sx) ($n) ($sy)) ↪ (let ex ≔ !run_evaluate ($sx) in (let en ≔ !run_evaluate ($n) in (let exl ≔ eo⋅⋅len ex in eo⋅⋅ite (eo⋅⋅or (eo⋅⋅gt (0) en) (eo⋅⋅gt en exl)) ex ((let ey ≔ !run_evaluate ($sy) in (let rc ≔ eo⋅⋅add (eo⋅⋅neg en) exl in eo⋅⋅concat (eo⋅⋅extract ex (0) (eo⋅⋅add en (-1))) (eo⋅⋅extract ey (0) (eo⋅⋅add rc (-1))) (eo⋅⋅extract ex (eo⋅⋅add en (eo⋅⋅len ey)) exl)))))))
with !run_evaluate (bvnot ($xb)) ↪ eo⋅⋅not (!run_evaluate ($xb))
with !run_evaluate (bvneg ($xb)) ↪ eo⋅⋅neg (!run_evaluate ($xb))
with !run_evaluate (bvadd ($xb) ($ybs)) ↪ eo⋅⋅add (!run_evaluate ($xb)) (!run_evaluate ($ybs))
with !run_evaluate (bvmul ($xb) ($ybs)) ↪ eo⋅⋅mul (!run_evaluate ($xb)) (!run_evaluate ($ybs))
with !run_evaluate (bvudiv ($xb) ($yb)) ↪ (let ex ≔ !run_evaluate ($xb) in (let ey ≔ !run_evaluate ($yb) in eo⋅⋅ite (eo⋅⋅eq (eo⋅⋅to_z ey) (0)) (!bv_ones (!bv_bitwidth (eo⋅⋅typeof ($xb)))) (eo⋅⋅zdiv ex ey)))
with !run_evaluate (bvurem ($xb) ($yb)) ↪ (let ex ≔ !run_evaluate ($xb) in (let ey ≔ !run_evaluate ($yb) in eo⋅⋅ite (eo⋅⋅eq (eo⋅⋅to_z ey) (0)) ex (eo⋅⋅zmod ex ey)))
with !run_evaluate (bvand ($xb) ($ybs)) ↪ eo⋅⋅and (!run_evaluate ($xb)) (!run_evaluate ($ybs))
with !run_evaluate (bvor ($xb) ($ybs)) ↪ eo⋅⋅or (!run_evaluate ($xb)) (!run_evaluate ($ybs))
with !run_evaluate (bvxor ($xb) ($ybs)) ↪ eo⋅⋅xor (!run_evaluate ($xb)) (!run_evaluate ($ybs))
with !run_evaluate (concat ($xb) ($zbs)) ↪ eo⋅⋅concat (!run_evaluate ($xb)) (!run_evaluate ($zbs))
with !run_evaluate (bvsub ($xb) ($yb)) ↪ eo⋅⋅add (!run_evaluate ($xb)) (eo⋅⋅neg (!run_evaluate ($yb)))
with !run_evaluate (extract ($m) ($n) ($xb)) ↪ eo⋅⋅extract (!run_evaluate ($xb)) ($n) ($m)
with !run_evaluate (and (bvult ($xb) ($yb))) ↪ !run_evaluate (bvugt ($yb) ($xb))
with !run_evaluate (bvule ($xb) ($yb)) ↪ !run_evaluate (bvuge ($yb) ($xb))
with !run_evaluate (bvugt ($xb) ($yb)) ↪ (let ex ≔ eo⋅⋅to_z (!run_evaluate ($xb)) in (let ey ≔ eo⋅⋅to_z (!run_evaluate ($yb)) in eo⋅⋅gt ex ey))
with !run_evaluate (bvuge ($xb) ($yb)) ↪ (let ex ≔ !run_evaluate ($xb) in (let ey ≔ !run_evaluate ($yb) in eo⋅⋅or (eo⋅⋅gt ex ey) (eo⋅⋅eq ex ey)))
with !run_evaluate (bvslt ($xb) ($yb)) ↪ !run_evaluate (bvsgt ($yb) ($xb))
with !run_evaluate (bvsle ($xb) ($yb)) ↪ !run_evaluate (bvsge ($yb) ($xb))
with !run_evaluate (bvsgt ($xb) ($yb)) ↪ (let ex ≔ !bv_to_signed_int (!run_evaluate ($xb)) in (let ey ≔ !bv_to_signed_int (!run_evaluate ($yb)) in eo⋅⋅gt ex ey))
with !run_evaluate (bvsge ($xb) ($yb)) ↪ (let ex ≔ !bv_to_signed_int (!run_evaluate ($xb)) in (let ey ≔ !bv_to_signed_int (!run_evaluate ($yb)) in eo⋅⋅or (eo⋅⋅gt ex ey) (eo⋅⋅eq ex ey)))
with !run_evaluate (bvshl ($xb) ($yb)) ↪ (let ex ≔ !run_evaluate ($xb) in (let ey ≔ !run_evaluate ($yb) in (let eyz ≔ eo⋅⋅to_z ey in (let w ≔ !bv_bitwidth (eo⋅⋅typeof ($xb)) in eo⋅⋅ite (eo⋅⋅gt eyz w) (eo⋅⋅to_bin w (0)) (eo⋅⋅to_bin w (eo⋅⋅mul (eo⋅⋅to_z ex) (!arith_eval_int_pow_2 eyz)))))))
with !run_evaluate (bvlshr ($xb) ($yb)) ↪ (let ex ≔ !run_evaluate ($xb) in (let ey ≔ !run_evaluate ($yb) in (let eyz ≔ eo⋅⋅to_z ey in (let w ≔ !bv_bitwidth (eo⋅⋅typeof ($xb)) in eo⋅⋅ite (eo⋅⋅gt eyz w) (eo⋅⋅to_bin w (0)) (eo⋅⋅to_bin w (eo⋅⋅zdiv (eo⋅⋅to_z ex) (!arith_eval_int_pow_2 eyz)))))))
with !run_evaluate (bvashr ($xb) ($yb)) ↪ (let ex ≔ !run_evaluate ($xb) in (let ey ≔ !run_evaluate ($yb) in (let sb ≔ !bv_sign_bit ex in eo⋅⋅ite (eo⋅⋅eq sb ()) (!run_evaluate (bvlshr ex ey)) (!run_evaluate (bvnot (bvlshr (bvnot ex) ey))))))
with !run_evaluate (repeat ($n) ($xb)) ↪ !run_evaluate (!bv_unfold_repeat (!run_evaluate ($n)) (!run_evaluate ($xb)))
with !run_evaluate (sign_extend ($n) ($xb)) ↪ (let ex ≔ !run_evaluate ($xb) in eo⋅⋅concat (!run_evaluate (!bv_unfold_repeat (!run_evaluate ($n)) (!bv_sign_bit ex))) ex)
with !run_evaluate (zero_extend ($n) ($xb)) ↪ (let ex ≔ !run_evaluate ($xb) in eo⋅⋅concat (!run_evaluate (!bv_unfold_repeat (!run_evaluate ($n)) ())) ex)
with !run_evaluate ({|@bv|} ($n) ($m)) ↪ eo⋅⋅to_bin (!run_evaluate ($m)) (!run_evaluate ($n))
with !run_evaluate ({|@bvsize|} ($xb)) ↪ !bv_bitwidth (eo⋅⋅typeof ($xb))
with !run_evaluate (int_to_bv ($n) ($m)) ↪ eo⋅⋅to_bin (!run_evaluate ($n)) (!run_evaluate ($m))
with !run_evaluate (ubv_to_int ($xb)) ↪ eo⋅⋅to_z (!run_evaluate ($xb))
with !run_evaluate (sbv_to_int ($xb)) ↪ (let ex ≔ !run_evaluate ($xb) in eo⋅⋅ite (eo⋅⋅eq (!bv_sign_bit ($xb)) ()) (eo⋅⋅to_z ex) (eo⋅⋅add (eo⋅⋅to_z ex) (eo⋅⋅neg (!arith_eval_int_pow_2 (!bv_bitwidth (eo⋅⋅typeof ($xb)))))))
with !run_evaluate ($z) ↪ $z;
sequential symbol !evaluate_list : τ ({|@List|} ⤳ {|@List|});
rule !evaluate_list ({|@list|} ($t) ($ts)) ↪ eo⋅⋅cons {|@list|} (!run_evaluate ($t)) (!evaluate_list ($ts))
with !evaluate_list {|@list.nil|} ↪ {|@list.nil|};
sequential symbol !get_aci_normal_form [T : Set]: τ (T ⤳ T);
rule !get_aci_normal_form (or ($b1) ($b2)) ↪ {|@aci.sorted|} or (!get_ai_norm (or ($b1) ($b2)))
with !get_aci_normal_form (and ($b1) ($b2)) ↪ {|@aci.sorted|} and (!get_ai_norm (and ($b1) ($b2)))
with !get_aci_normal_form (re⋅union ($r1) ($r2)) ↪ {|@aci.sorted|} re⋅union (!get_ai_norm (re⋅union ($r1) ($r2)))
with !get_aci_normal_form (re⋅inter ($r1) ($r2)) ↪ {|@aci.sorted|} re⋅inter (!get_ai_norm (re⋅inter ($r1) ($r2)))
with !get_aci_normal_form (bvor ($xb1) ($xb2)) ↪ {|@aci.sorted|} bvor (!get_ai_norm (bvor ($xb1) ($xb2)))
with !get_aci_normal_form (bvand ($xb1) ($xb2)) ↪ {|@aci.sorted|} bvand (!get_ai_norm (bvand ($xb1) ($xb2)))
with !get_aci_normal_form (bvxor ($xb1) ($xb2)) ↪ {|@aci.sorted|} bvxor (!get_a_norm (bvxor ($xb1) ($xb2)))
with !get_aci_normal_form (str⋅++ ($xs1) ($xs2)) ↪ !get_a_norm (str⋅++ ($xs1) ($xs2))
with !get_aci_normal_form (re⋅++ ($r1) ($r2)) ↪ !get_a_norm (re⋅++ ($r1) ($r2))
with !get_aci_normal_form (concat ($xb1) ($xb2)) ↪ !get_a_norm (concat ($xb1) ($xb2))
with !get_aci_normal_form ($x) ↪ $x;
sequential symbol !is_absorb_rec [U : Set] [V : Set] [W : Set]: τ ((U ⤳ U ⤳ U) ⤳ V ⤳ W ⤳ Bool);
rule !is_absorb_rec ($f) ($zero) ($zero) ↪ true
with !is_absorb_rec ($f) ($f ($a) ($b)) ($zero) ↪ eo⋅⋅ite (!is_absorb_rec ($f) ($a) ($zero)) true (!is_absorb_rec ($f) ($b) ($zero))
with !is_absorb_rec ($f) ($b) ($zero) ↪ false;
sequential symbol !get_zero [S : Set]: τ (S ⤳ S);
rule !get_zero (or ($b1) ($b2)) ↪ true
with !get_zero (and ($b1) ($b2)) ↪ false
with !get_zero (re⋅union ($r1) ($r2)) ↪ re⋅all
with !get_zero (re⋅inter ($r1) ($r2)) ↪ re⋅none
with !get_zero (re⋅++ ($r1) ($r2)) ↪ re⋅none
with !get_zero (bvor ($xb1) ($xb2)) ↪ !bv_ones (!bv_bitwidth (eo⋅⋅typeof ($xb1)))
with !get_zero (bvand ($xb1) ($xb2)) ↪ eo⋅⋅to_bin (!bv_bitwidth (eo⋅⋅typeof ($xb1))) (0);
sequential symbol !is_absorb [T : Set]: τ (T ⤳ T ⤳ Bool);
rule !is_absorb ($f ($t1) ($t2)) ($zero) ↪ !is_absorb_rec ($f) ($f ($t1) ($t2)) ($zero);
sequential symbol !compute_card : τ (eo⋅⋅Type ⤳ Int);
rule !compute_card Bool ↪ 2
with !compute_card (BitVec ($n)) ↪ !arith_eval_int_pow_2 ($n);
