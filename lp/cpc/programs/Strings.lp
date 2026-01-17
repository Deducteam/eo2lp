require open cpc.Core Stdlib.Set cpc.theories.Arith cpc.theories.Builtin cpc.theories.Quantifiers cpc.theories.Strings cpc.programs.Nary cpc.programs.PolyNorm cpc.programs.DistinctValues;
sequential symbol !str_is_empty [U : Set]: τ ((Seq U) ⤳ Bool);
rule !str_is_empty ({|as|} seq⋅empty (Seq ($U))) ↪ true
with !str_is_empty ("") ↪ true
with !str_is_empty ($x) ↪ false;
sequential symbol !seq_element_of_unit [U : Set]: τ ((Seq U) ⤳ U);
rule !seq_element_of_unit (seq⋅unit ($x)) ↪ $x;
sequential symbol !str_value_len [T : Set]: τ ((Seq T) ⤳ Int);
rule !str_value_len (seq⋅++ (seq⋅unit ($e)) ($ss)) ↪ eo⋅⋅add (1) (!str_value_len ($ss))
with !str_value_len ({|as|} seq⋅empty (Seq ($T))) ↪ 0
with !str_value_len (seq⋅unit ($e)) ↪ 1
with !str_value_len ($s) ↪ eo⋅⋅requires (eo⋅⋅is_str ($s)) true (eo⋅⋅len ($s));
sequential symbol !char_type_of : τ (eo⋅⋅Type ⤳ eo⋅⋅Type);
rule !char_type_of (Seq ($U)) ↪ $U;
symbol !str_concat [T : Set] (x : τ (Seq T)) (y : τ (Seq T))≔ eo⋅⋅list_concat str⋅++ x y;
symbol !str_head [T : Set] (x : τ (Seq T))≔ eo⋅⋅list_nth str⋅++ x (0);
symbol !str_cons [T : Set] (x : τ (Seq T)) (y : τ (Seq T))≔ eo⋅⋅cons str⋅++ x y;
symbol !str_is_code_point (n : τ Int)≔ eo⋅⋅ite (eo⋅⋅is_z n) (eo⋅⋅ite (!compare_geq (196608) n) (eo⋅⋅not (eo⋅⋅is_neg n)) false) false;
symbol !str_self_if_empty [T : Set] (t : τ T)≔ eo⋅⋅requires t (!seq_empty (eo⋅⋅typeof t)) t;
sequential symbol !str_fixed_len_re : τ (RegLan ⤳ Int);
rule !str_fixed_len_re (re⋅++ ($r) ($r1)) ↪ eo⋅⋅add (!str_fixed_len_re ($r)) (!str_fixed_len_re ($r1))
with !str_fixed_len_re re⋅allchar ↪ 1
with !str_fixed_len_re (re⋅range ($s1) ($s2)) ↪ 1
with !str_fixed_len_re (str⋅to_re ($s1)) ↪ eo⋅⋅len ($s1)
with !str_fixed_len_re (re⋅union ($r) ($r1)) ↪ (let n ≔ !str_fixed_len_re ($r) in eo⋅⋅ite (eo⋅⋅eq ($r1) re⋅none) n (eo⋅⋅requires (!str_fixed_len_re ($r1)) n n))
with !str_fixed_len_re (re⋅inter ($r) ($r1)) ↪ (let n ≔ !str_fixed_len_re ($r) in eo⋅⋅ite (eo⋅⋅eq ($r1) re⋅all) n (eo⋅⋅requires (!str_fixed_len_re ($r1)) n n));
symbol !str_is_char_range (s1 : τ String) (s2 : τ String)≔ eo⋅⋅and (eo⋅⋅is_eq (eo⋅⋅len s1) (1)) (eo⋅⋅is_eq (eo⋅⋅len s2) (1));
sequential symbol !str_membership_str : τ (Bool ⤳ String);
rule !str_membership_str (str⋅in_re ($s) ($r)) ↪ $s;
sequential symbol !str_membership_re : τ (Bool ⤳ RegLan);
rule !str_membership_re (str⋅in_re ($s) ($r)) ↪ $r;
sequential symbol !re_nullable : τ (RegLan ⤳ Bool);
rule !re_nullable re⋅all ↪ true
with !re_nullable {|@re.empty|} ↪ true
with !re_nullable (re⋅* ($r)) ↪ true
with !re_nullable (re⋅union ($r) ($rr)) ↪ eo⋅⋅or (!re_nullable ($r)) (!re_nullable ($rr))
with !re_nullable (re⋅inter ($r) ($rr)) ↪ eo⋅⋅and (!re_nullable ($r)) (!re_nullable ($rr))
with !re_nullable (re⋅++ ($r) ($rr)) ↪ eo⋅⋅and (!re_nullable ($r)) (!re_nullable ($rr))
with !re_nullable (re⋅comp ($r)) ↪ eo⋅⋅not (!re_nullable ($r))
with !re_nullable ($r) ↪ false;
sequential symbol !re_ac_merge : τ ((RegLan ⤳ RegLan ⤳ RegLan) ⤳ RegLan ⤳ RegLan ⤳ RegLan);
rule !re_ac_merge re⋅union re⋅none ($r1) ↪ $r1
with !re_ac_merge re⋅inter re⋅none ($r1) ↪ re⋅none
with !re_ac_merge ($f) ($r1) ($r1) ↪ $r1
with !re_ac_merge ($f) ($f ($r1) ($rr1)) ($f ($r2) ($rr2)) ↪ eo⋅⋅list_concat ($f) (eo⋅⋅list_diff ($f) ($f ($r1) ($rr1)) ($f ($r2) ($rr2))) ($f ($r2) ($rr2))
with !re_ac_merge ($f) ($f ($r1) ($rr1)) ($r2) ↪ eo⋅⋅ite (eo⋅⋅is_neg (eo⋅⋅list_find ($f) ($f ($r1) ($rr1)) ($r2))) (eo⋅⋅cons ($f) ($r2) ($f ($r1) ($rr1))) ($f ($r1) ($rr1))
with !re_ac_merge ($f) ($r2) ($f ($r1) ($rr1)) ↪ eo⋅⋅ite (eo⋅⋅is_neg (eo⋅⋅list_find ($f) ($f ($r1) ($rr1)) ($r2))) (eo⋅⋅cons ($f) ($r2) ($f ($r1) ($rr1))) ($f ($r1) ($rr1))
with !re_ac_merge ($f) ($r1) ($r2) ↪ $f ($r1) ($f ($r2) (eo⋅⋅nil ($f) RegLan));
sequential symbol !re_concat_merge : τ (RegLan ⤳ RegLan ⤳ RegLan);
rule !re_concat_merge (re⋅++ ($r1) ($rr1)) (re⋅++ ($r2) ($rr2)) ↪ eo⋅⋅list_concat re⋅++ (re⋅++ ($r1) ($rr1)) (re⋅++ ($r2) ($rr2))
with !re_concat_merge re⋅none ($r1) ↪ re⋅none
with !re_concat_merge ($r1) (re⋅++ ($r2) ($rr2)) ↪ eo⋅⋅cons re⋅++ ($r1) (re⋅++ ($r2) ($rr2))
with !re_concat_merge {|@re.empty|} ($r1) ↪ $r1
with !re_concat_merge ($r1) {|@re.empty|} ↪ $r1
with !re_concat_merge ($r1) ($r2) ↪ re⋅++ ($r1) (re⋅++ ($r2) {|@re.empty|});
sequential symbol !derivative : τ (String ⤳ RegLan ⤳ RegLan);
rule !derivative ($c) (re⋅union ($r) ($rr)) ↪ !re_ac_merge re⋅union (!derivative ($c) ($r)) (!derivative ($c) ($rr))
with !derivative ($c) (re⋅++ ($r) ($rr)) ↪ eo⋅⋅ite (!re_nullable ($r)) (!re_ac_merge re⋅union (!derivative ($c) ($rr)) (!re_concat_merge (!derivative ($c) ($r)) ($rr))) (!re_concat_merge (!derivative ($c) ($r)) ($rr))
with !derivative ($c) (re⋅inter ($r) ($rr)) ↪ !re_ac_merge re⋅inter (!derivative ($c) ($r)) (!derivative ($c) ($rr))
with !derivative ($c) (re⋅comp ($r)) ↪ re⋅comp (!derivative ($c) ($r))
with !derivative ($c) (re⋅* ($r)) ↪ !re_concat_merge (!derivative ($c) ($r)) (re⋅* ($r))
with !derivative ($c) (str⋅to_re ($s1)) ↪ eo⋅⋅ite (eo⋅⋅is_eq (eo⋅⋅extract ($s1) (0) (0)) ($c)) (str⋅to_re (eo⋅⋅extract ($s1) (1) (eo⋅⋅add (-1) (eo⋅⋅len ($s1))))) re⋅none
with !derivative ($c) (re⋅range ($s1) ($s2)) ↪ eo⋅⋅ite (eo⋅⋅and (!compare_geq (eo⋅⋅to_z ($c)) (eo⋅⋅to_z ($s1))) (!compare_geq (eo⋅⋅to_z ($s2)) (eo⋅⋅to_z ($c)))) {|@re.empty|} re⋅none
with !derivative ($c) re⋅none ↪ re⋅none
with !derivative ($c) {|@re.empty|} ↪ re⋅none
with !derivative ($c) re⋅all ↪ re⋅all
with !derivative ($c) re⋅allchar ↪ {|@re.empty|};
sequential symbol !str_eval_str_in_re : τ (String ⤳ RegLan ⤳ Bool);
rule !str_eval_str_in_re ("") ($r) ↪ !re_nullable ($r)
with !str_eval_str_in_re ($s) re⋅none ↪ false
with !str_eval_str_in_re ($s) ($r) ↪ !str_eval_str_in_re (eo⋅⋅extract ($s) (1) (eo⋅⋅add (-1) (eo⋅⋅len ($s)))) (!derivative (eo⋅⋅extract ($s) (0) (0)) ($r));
sequential symbol !str_first_match_rec_smallest : τ (String ⤳ RegLan ⤳ Int ⤳ Int ⤳ Int);
rule !str_first_match_rec_smallest ($s) ($r) ($m) ($lens) ↪ (let ss ≔ eo⋅⋅extract ($s) (0) (eo⋅⋅add ($m) (-1)) in eo⋅⋅ite (!str_eval_str_in_re ss ($r)) ($m) (eo⋅⋅requires (eo⋅⋅eq ($m) ($lens)) false (!str_first_match_rec_smallest ($s) ($r) (eo⋅⋅add ($m) (1)) ($lens))));
sequential symbol !str_first_match_rec : τ (String ⤳ RegLan ⤳ RegLan ⤳ Int ⤳ Int ⤳ {|@Pair|} Int Int);
rule !str_first_match_rec ($s) ($r) ($rs) ($n) ($lens) ↪ eo⋅⋅ite (!str_eval_str_in_re ($s) ($rs)) ({|@pair|} ($n) (eo⋅⋅add ($n) (!str_first_match_rec_smallest ($s) ($r) (0) ($lens)))) (eo⋅⋅ite (eo⋅⋅eq ($lens) (0)) ({|@pair|} (-1) (-1)) ((let lsm1 ≔ eo⋅⋅add ($lens) (-1) in !str_first_match_rec (eo⋅⋅extract ($s) (1) lsm1) ($r) ($rs) (eo⋅⋅add ($n) (1)) lsm1)));
symbol !str_first_match (s : τ String) (r : τ RegLan)≔ (let lens ≔ eo⋅⋅len s in (let rs ≔ re⋅++ r (re⋅++ re⋅all {|@re.empty|}) in eo⋅⋅requires (eo⋅⋅is_str s) true (!str_first_match_rec s r rs (0) lens)));
symbol !str_prefix [U : Set] (s : τ (Seq U)) (n : τ Int)≔ str⋅substr s (0) n;
symbol !str_suffix_rem [U : Set] (s : τ (Seq U)) (n : τ Int)≔ str⋅substr s n (- (str⋅len s) n);
symbol !str_prefix_rem [U : Set] (s : τ (Seq U)) (n : τ Int)≔ str⋅substr s (0) (- (str⋅len s) n);
symbol !str_suffix [U : Set] (s : τ (Seq U)) (n : τ Int)≔ str⋅substr s (- (str⋅len s) n) n;
sequential symbol !str_unify_split [U : Set]: τ ((Seq U) ⤳ (Seq U) ⤳ Bool ⤳ Seq U);
rule !str_unify_split ($t) ($s) true ↪ ite (and (>= (str⋅len ($t)) (str⋅len ($s)))) (!str_prefix ($t) (- (str⋅len ($t)) (str⋅len ($s)))) (!str_prefix ($s) (- (str⋅len ($s)) (str⋅len ($t))))
with !str_unify_split ($t) ($s) false ↪ ite (and (>= (str⋅len ($t)) (str⋅len ($s)))) (!str_suffix_rem ($t) (str⋅len ($s))) (!str_suffix_rem ($s) (str⋅len ($t)));
symbol !str_first_ctn_pre [U : Set] (s : τ (Seq U)) (t : τ (Seq U))≔ !str_prefix s (str⋅indexof s t (0));
symbol !str_first_ctn_post [U : Set] (s : τ (Seq U)) (t : τ (Seq U))≔ !str_suffix_rem s (+ (str⋅len ({|@purify|} (!str_first_ctn_pre s t))) (+ (str⋅len t) (0)));
symbol !re_first_match_pre (s : τ String) (r : τ RegLan)≔ !str_prefix s (str⋅indexof_re s r (0));
symbol !re_first_match (s : τ String) (r : τ RegLan)≔ (let n ≔ str⋅indexof_re s r (0) in str⋅substr s n (- ({|@strings_occur_index_re|} s r (1)) n));
symbol !re_first_match_post (s : τ String) (r : τ RegLan)≔ !str_suffix_rem s ({|@strings_occur_index_re|} s r (1));
symbol !str_rev [U : Set] (rev : τ Bool) (t : τ (Seq U))≔ eo⋅⋅ite rev (eo⋅⋅list_rev str⋅++ t) t;
symbol !str_re_rev (rev : τ Bool) (t : τ RegLan)≔ eo⋅⋅ite rev (eo⋅⋅list_rev re⋅++ t) t;
sequential symbol !str_nary_intro [T : Set]: τ ((Seq T) ⤳ Seq T);
rule !str_nary_intro (str⋅++ ($t) ($ss)) ↪ str⋅++ ($t) ($ss)
with !str_nary_intro ($t) ↪ (let nil ≔ !seq_empty (eo⋅⋅typeof ($t)) in eo⋅⋅ite (eo⋅⋅eq ($t) nil) ($t) (!str_cons ($t) nil));
sequential symbol !re_nary_intro : τ (RegLan ⤳ RegLan);
rule !re_nary_intro (re⋅++ ($t) ($ss)) ↪ re⋅++ ($t) ($ss)
with !re_nary_intro {|@re.empty|} ↪ {|@re.empty|}
with !re_nary_intro ($t) ↪ eo⋅⋅cons re⋅++ ($t) {|@re.empty|};
sequential symbol !str_nary_elim [T : Set]: τ ((Seq T) ⤳ Seq T);
rule !str_nary_elim (str⋅++ ($t) ($ss)) ↪ (let nil ≔ !seq_empty (eo⋅⋅typeof ($t)) in eo⋅⋅ite (eo⋅⋅eq ($ss) nil) ($t) (str⋅++ ($t) ($ss)))
with !str_nary_elim ($t) ↪ !str_self_if_empty ($t);
sequential symbol !re_nary_elim : τ (RegLan ⤳ RegLan);
rule !re_nary_elim (re⋅++ ($t) ($ss)) ↪ eo⋅⋅ite (eo⋅⋅eq ($ss) {|@re.empty|}) ($t) (re⋅++ ($t) ($ss))
with !re_nary_elim ($t) ↪ $t;
symbol !str_reduction_pred_case_conv (k : τ String) (x : τ String) (isLower : τ Bool)≔ and (and (= (str⋅len x) (str⋅len k))) (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) (or (not (and (>= {|@var.str_index|} (0)))) (not (and (< {|@var.str_index|} (str⋅len k)))) (and (= (str⋅to_code (str⋅substr k {|@var.str_index|} (1))) ((let ci ≔ str⋅to_code (str⋅substr x {|@var.str_index|} (1)) in eo⋅⋅ite isLower (ite (and (and (<= (65) ci)) (and (<= ci (90)))) (+ ci (+ (32) (0))) ci) (ite (and (and (<= (97) ci)) (and (<= ci (122)))) (+ ci (+ (-32) (0))) ci)))))));
sequential symbol !str_reduction_pred [T : Set]: τ (T ⤳ Bool);
rule !str_reduction_pred (str⋅contains ($x) ($y)) ↪ (let k ≔ {|@purify|} (str⋅contains ($x) ($y)) in and (= k (not (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) (or (not (and (>= {|@var.str_index|} (0)))) (not (and (<= {|@var.str_index|} (- (str⋅len ($x)) (str⋅len ($y)))))) (not (and (= (str⋅substr ($x) {|@var.str_index|} (str⋅len ($y))) ($y)))))))))
with !str_reduction_pred (str⋅substr ($x) ($n) ($m)) ↪ (let k ≔ {|@purify|} (str⋅substr ($x) ($n) ($m)) in (let npm ≔ + ($n) (+ ($m) (0)) in (let k1 ≔ {|@purify|} (!str_prefix ($x) ($n)) in (let k2 ≔ {|@purify|} (!str_suffix_rem ($x) npm) in ite (and (and (>= ($n) (0))) (and (> (str⋅len ($x)) ($n))) (and (> ($m) (0)))) (and (and (= ($x) (str⋅++ k1 (str⋅++ k (str⋅++ k2 (!seq_empty (Seq T))))))) (and (= (str⋅len k1) ($n))) (or (and (= (str⋅len k2) (- (str⋅len ($x)) npm))) (and (= (str⋅len k2) (0)))) (and (<= (str⋅len k) ($m)))) (and (= k (!seq_empty (eo⋅⋅typeof ($x)))))))))
with !str_reduction_pred (str⋅indexof ($x) ($y) ($n)) ↪ (let k ≔ {|@purify|} (str⋅indexof ($x) ($y) ($n)) in (let xn ≔ str⋅substr ($x) ($n) (- (str⋅len ($x)) ($n)) in (let k1 ≔ {|@purify|} (!str_first_ctn_pre xn ($y)) in (let k2 ≔ {|@purify|} (!str_first_ctn_post xn ($y)) in ite (or (not (str⋅contains xn ($y))) (and (> ($n) (str⋅len ($x)))) (and (> (0) ($n)))) (and (= k (-1))) (ite (and (= ($y) (!seq_empty (eo⋅⋅typeof ($x))))) (and (= k ($n))) (and (and (= xn (str⋅++ k1 (str⋅++ ($y) (str⋅++ k2 (!seq_empty (Seq T))))))) (not (str⋅contains (str⋅++ k1 (str⋅++ (str⋅substr ($y) (0) (- (str⋅len ($y)) (1))) (!seq_empty (Seq T)))) ($y))) (and (= k (+ ($n) (+ (str⋅len k1) (0)))))))))))
with !str_reduction_pred (str⋅replace ($x) ($y) ($z)) ↪ (let k ≔ {|@purify|} (str⋅replace ($x) ($y) ($z)) in ite (and (= ($y) (!seq_empty (eo⋅⋅typeof ($y))))) (and (= k (str⋅++ ($z) (str⋅++ ($x) (!seq_empty (Seq T)))))) (ite (str⋅contains ($x) ($y)) ((let k1 ≔ {|@purify|} (!str_first_ctn_pre ($x) ($y)) in (let k2 ≔ {|@purify|} (!str_first_ctn_post ($x) ($y)) in and (and (= ($x) (str⋅++ k1 (str⋅++ ($y) (str⋅++ k2 (!seq_empty (Seq T))))))) (and (= k (str⋅++ k1 (str⋅++ ($z) (str⋅++ k2 (!seq_empty (Seq T))))))) (not (str⋅contains (str⋅++ k1 (str⋅++ (str⋅substr ($y) (0) (- (str⋅len ($y)) (1))) (!seq_empty (Seq T)))) ($y)))))) (and (= k ($x)))))
with !str_reduction_pred (str⋅from_int ($n)) ↪ (let k ≔ {|@purify|} (str⋅from_int ($n)) in (let R ≔ {|@strings_itos_result|} ($n) in ite (and (>= ($n) (0))) (and (and (>= (str⋅len k) (1))) (and (= ($n) (R (str⋅len k)))) (and (= (0) (R (0)))) (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) ((let cd ≔ - (str⋅to_code (str⋅substr k {|@var.str_index|} (1))) (48) in (let ux1 ≔ R (+ {|@var.str_index|} (+ (1) (0))) in or (not (and (>= {|@var.str_index|} (0)))) (not (and (< {|@var.str_index|} (str⋅len k)))) (and (and (= ux1 (+ cd (+ (* (10) (* (R {|@var.str_index|}) (1))) (0))))) (and (and (>= cd (ite (and (and (= {|@var.str_index|} (0))) (and (> (str⋅len k) (1)))) (1) (0)))) (and (< cd (10)))) (and (>= ($n) ux1)))))))) (and (= k ("")))))
with !str_reduction_pred (str⋅to_int ($s)) ↪ (let k ≔ {|@purify|} (str⋅to_int ($s)) in (let xlen ≔ str⋅len ($s) in (let R ≔ {|@strings_stoi_result|} ($s) in (let ndi ≔ {|@strings_stoi_non_digit|} ($s) in ite (and (< k (0))) ((let ndc ≔ - (str⋅to_code (str⋅substr ($s) ndi (1))) (48) in and (and (= k (-1))) (or (and (= ($s) (""))) (and (and (>= ndi (0))) (and (< ndi xlen)) (or (and (< ndc (0))) (and (>= ndc (10)))))))) (and (and (= k (R xlen))) (and (= (0) (R (0)))) (and (> (str⋅len ($s)) (0))) (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) ((let cd ≔ - (str⋅to_code (str⋅substr ($s) {|@var.str_index|} (1))) (48) in (let ux1 ≔ R (+ {|@var.str_index|} (+ (1) (0))) in or (not (and (>= {|@var.str_index|} (0)))) (not (and (< {|@var.str_index|} (str⋅len ($s))))) (and (and (= ux1 (+ cd (+ (* (10) (* (R {|@var.str_index|}) (1))) (0))))) (and (and (>= cd (0))) (and (< cd (10)))) (and (>= k ux1))))))))))))
with !str_reduction_pred (seq⋅nth ($x) ($n)) ↪ (let k ≔ {|@purify|} (seq⋅nth ($x) ($n)) in (let k1 ≔ {|@purify|} (!str_prefix ($x) ($n)) in (let k2 ≔ {|@purify|} (!str_suffix_rem ($x) (+ ($n) (+ (1) (0)))) in => (and (and (>= ($n) (0))) (and (> (str⋅len ($x)) ($n)))) (and (and (= ($x) (str⋅++ k1 (str⋅++ (seq⋅unit k) (str⋅++ k2 (!seq_empty (Seq T))))))) (and (= (str⋅len k1) ($n))) (and (= (str⋅len k2) (- (str⋅len ($x)) (+ ($n) (+ (1) (0))))))))))
with !str_reduction_pred (str⋅update ($x) ($n) ($y)) ↪ (let k ≔ {|@purify|} (str⋅update ($x) ($n) ($y)) in ite (and (and (>= ($n) (0))) (and (> (str⋅len ($x)) ($n)))) ((let k1 ≔ {|@purify|} (!str_prefix ($x) ($n)) in (let ys ≔ eo⋅⋅ite (eo⋅⋅is_eq (!str_value_len ($y)) (1)) ($y) (str⋅substr ($y) (0) (- (str⋅len ($x)) ($n))) in (let k2 ≔ {|@purify|} (!str_suffix_rem ($x) (+ ($n) (+ (str⋅len ys) (0)))) in (let k3 ≔ {|@purify|} (str⋅substr ($x) ($n) (str⋅len ys)) in and (and (= k (str⋅++ k1 (str⋅++ ys (str⋅++ k2 (!seq_empty (Seq T))))))) (and (= ($x) (str⋅++ k1 (str⋅++ k3 (str⋅++ k2 (!seq_empty (Seq T))))))) (and (= (str⋅len k1) ($n))) (and (= (str⋅len ys) (str⋅len k3)))))))) (and (= k ($x))))
with !str_reduction_pred (str⋅replace_all ($x) ($y) ($z)) ↪ (let k ≔ {|@purify|} (str⋅replace_all ($x) ($y) ($z)) in (let numOcc ≔ {|@strings_num_occur|} ($x) ($y) in (let result ≔ {|@strings_replace_all_result|} (str⋅replace_all ($x) ($y) ($z)) in (let occIndex ≔ {|@strings_occur_index|} ($x) ($y) in ite (and (= ($y) (!seq_empty (eo⋅⋅typeof ($x))))) (and (= k ($x))) (and (and (>= numOcc (0))) (and (= k (result (0)))) (and (= (result numOcc) (str⋅substr ($x) (occIndex numOcc) (str⋅len ($x))))) (and (= (occIndex (0)) (0))) (and (= (str⋅indexof ($x) ($y) (occIndex numOcc)) (-1))) (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) (or (not (and (>= {|@var.str_index|} (0)))) (not (and (< {|@var.str_index|} numOcc))) ((let ii ≔ str⋅indexof ($x) ($y) (occIndex {|@var.str_index|}) in (let oi ≔ occIndex {|@var.str_index|} in and (not (and (= ii (-1)))) (and (= (result {|@var.str_index|}) (str⋅++ (str⋅substr ($x) oi (- ii oi)) (str⋅++ ($z) (str⋅++ (result (+ {|@var.str_index|} (+ (1) (0)))) (!seq_empty (Seq T))))))) (and (= (occIndex (+ {|@var.str_index|} (+ (1) (0)))) (+ ii (+ (str⋅len ($y)) (0)))))))))))))))
with !str_reduction_pred (str⋅replace_re ($s) ($r) ($t)) ↪ (let k ≔ {|@purify|} (str⋅replace_re ($s) ($r) ($t)) in (let k1 ≔ {|@purify|} (!re_first_match_pre ($s) ($r)) in (let k2 ≔ {|@purify|} (!re_first_match ($s) ($r)) in (let k3 ≔ {|@purify|} (!re_first_match_post ($s) ($r)) in ite (and (= (str⋅indexof_re ($s) ($r) (0)) (-1))) (and (= k ($s))) (and (and (= ($s) (str⋅++ k1 (str⋅++ k2 (str⋅++ k3 (!seq_empty (Seq T))))))) (and (= (str⋅len k1) (str⋅indexof_re ($s) ($r) (0)))) (forall ({|@list|} (eo⋅⋅var ("@var.str_length") Int)) (or (not (and (>= {|@var.str_length|} (0)))) (not (and (< {|@var.str_length|} (str⋅len k2)))) (not (str⋅in_re (str⋅substr k2 (0) {|@var.str_length|}) ($r))))) (str⋅in_re k2 ($r)) (and (= k (str⋅++ k1 (str⋅++ ($t) (str⋅++ k3 (!seq_empty (Seq T))))))))))))
with !str_reduction_pred (str⋅replace_re_all ($s) ($r) ($t)) ↪ (let k ≔ {|@purify|} (str⋅replace_re_all ($s) ($r) ($t)) in (let numOcc ≔ {|@strings_num_occur_re|} ($s) ($r) in (let result ≔ {|@strings_replace_all_result|} (str⋅replace_re_all ($s) ($r) ($t)) in (let occIndex ≔ {|@strings_occur_index_re|} ($s) ($r) in (let rnemp ≔ re⋅diff ($r) (str⋅to_re ("")) in (let ssl ≔ str⋅substr ($s) (occIndex numOcc) (str⋅len ($s)) in ite (and (= (str⋅indexof_re ($s) rnemp (0)) (-1))) (and (= k ($s))) (and (and (> numOcc (0))) (and (= k (result (0)))) (and (= (result numOcc) ssl)) (and (= (occIndex (0)) (0))) (and (= (str⋅indexof_re ssl rnemp (0)) (-1))) (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) ((let ip1 ≔ + {|@var.str_index|} (+ (1) (0)) in or (not (and (>= {|@var.str_index|} (0)))) (not (and (< {|@var.str_index|} numOcc))) ((let oindex ≔ occIndex {|@var.str_index|} in (let ii ≔ str⋅indexof_re ($s) rnemp oindex in (let oindex1 ≔ occIndex ip1 in (let olen1 ≔ - oindex1 ii in and (and (> olen1 (0))) (str⋅in_re (str⋅substr ($s) ii olen1) rnemp) (forall ({|@list|} (eo⋅⋅var ("@var.str_length") Int)) (or (not (and (> {|@var.str_length|} (0)))) (not (and (< {|@var.str_length|} olen1))) (not (str⋅in_re (str⋅substr ($s) ii {|@var.str_length|}) ($r))))) (and (= (result {|@var.str_index|}) (str⋅++ (str⋅substr ($s) oindex (- ii oindex)) (str⋅++ ($t) (str⋅++ (result (+ {|@var.str_index|} (+ (1) (0)))) (!seq_empty (Seq T))))))))))))))))))))))
with !str_reduction_pred (str⋅indexof_re ($s) ($r) ($n)) ↪ (let k ≔ {|@purify|} (str⋅indexof_re ($s) ($r) ($n)) in ite (or (and (> ($n) (str⋅len ($s)))) (and (> (0) ($n)))) (and (= k (-1))) (ite (str⋅in_re ("") ($r)) (and (= k ($n))) (and (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int) (eo⋅⋅var ("@var.str_length") Int)) (or (not (and (>= {|@var.str_index|} ($n)))) (not (and (< {|@var.str_index|} (ite (and (= k (-1))) (str⋅len ($s)) k)))) (not (and (> {|@var.str_length|} (0)))) (not (and (<= {|@var.str_length|} (- (str⋅len ($s)) {|@var.str_index|})))) (not (str⋅in_re (str⋅substr ($s) {|@var.str_index|} {|@var.str_length|}) ($r))))) (or (and (= k (-1))) (and (and (>= k ($n))) (not (forall ({|@list|} (eo⋅⋅var ("@var.str_length") Int)) (or (not (and (>= {|@var.str_length|} (0)))) (not (and (<= {|@var.str_length|} (- (str⋅len ($s)) k)))) (not (str⋅in_re (str⋅substr ($s) k {|@var.str_length|}) ($r)))))))))))
with !str_reduction_pred (str⋅<= ($s) ($t)) ↪ (let k ≔ {|@purify|} (str⋅<= ($s) ($t)) in ite (and (= ($s) ($t))) k (not (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) (or (not (and (>= {|@var.str_index|} (0)))) (not (and (<= {|@var.str_index|} (str⋅len ($s))))) (not (and (<= {|@var.str_index|} (str⋅len ($t))))) (not (and (= (str⋅substr ($s) (0) {|@var.str_index|}) (str⋅substr ($t) (0) {|@var.str_index|})))) (ite k (and (>= (str⋅to_code (str⋅substr ($s) {|@var.str_index|} (1))) (str⋅to_code (str⋅substr ($t) {|@var.str_index|} (1))))) (and (>= (str⋅to_code (str⋅substr ($t) {|@var.str_index|} (1))) (str⋅to_code (str⋅substr ($s) {|@var.str_index|} (1))))))))))
with !str_reduction_pred (str⋅to_lower ($s)) ↪ !str_reduction_pred_case_conv ({|@purify|} (str⋅to_lower ($s))) ($s) true
with !str_reduction_pred (str⋅to_upper ($s)) ↪ !str_reduction_pred_case_conv ({|@purify|} (str⋅to_upper ($s))) ($s) false
with !str_reduction_pred (str⋅rev ($x)) ↪ (let k ≔ {|@purify|} (str⋅rev ($x)) in and (and (= (str⋅len ($x)) (str⋅len k))) (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) (or (not (and (>= {|@var.str_index|} (0)))) (not (and (< {|@var.str_index|} (str⋅len k)))) (and (= (str⋅substr k {|@var.str_index|} (1)) (str⋅substr ($x) (- (str⋅len ($x)) (+ {|@var.str_index|} (+ (1) (0)))) (1)))))));
sequential symbol !mk_str_eager_reduction [U : Set]: τ (U ⤳ Bool);
rule !mk_str_eager_reduction (str⋅from_code ($n)) ↪ (let k ≔ {|@purify|} (str⋅from_code ($n)) in ite (and (and (<= (0) ($n))) (and (< ($n) (196608)))) (and (= ($n) (str⋅to_code k))) (and (= k (""))))
with !mk_str_eager_reduction (str⋅to_code ($s)) ↪ (let t ≔ str⋅to_code ($s) in ite (and (= (str⋅len ($s)) (1))) (and (and (>= t (0))) (and (< t (196608)))) (and (= t (eo⋅⋅neg (1)))))
with !mk_str_eager_reduction (str⋅to_int ($s)) ↪ and (>= (str⋅to_int ($s)) (-1))
with !mk_str_eager_reduction (str⋅contains ($x) ($y)) ↪ (let k1 ≔ {|@purify|} (!str_first_ctn_pre ($x) ($y)) in (let k2 ≔ {|@purify|} (!str_first_ctn_post ($x) ($y)) in ite (str⋅contains ($x) ($y)) (and (= ($x) (str⋅++ k1 (str⋅++ ($y) (str⋅++ k2 (!seq_empty (Seq T))))))) (not (and (= ($x) ($y))))))
with !mk_str_eager_reduction (str⋅indexof ($x) ($y) ($n)) ↪ (let t ≔ str⋅indexof ($x) ($y) ($n) in and (or (and (= t (eo⋅⋅neg (1)))) (and (>= t ($n)))) (and (<= t (str⋅len ($x)))))
with !mk_str_eager_reduction (str⋅indexof_re ($s) ($r) ($n)) ↪ (let t ≔ str⋅indexof_re ($s) ($r) ($n) in and (or (and (= t (eo⋅⋅neg (1)))) (and (>= t ($n)))) (and (<= t (str⋅len ($s)))))
with !mk_str_eager_reduction (str⋅in_re ($s) ($r)) ↪ => (str⋅in_re ($s) ($r)) (and (= (str⋅len ($s)) (!str_fixed_len_re ($r))));
sequential symbol !re_unfold_pos_concat_rec : τ (String ⤳ RegLan ⤳ RegLan ⤳ Int ⤳ {|@Pair|} String Bool);
rule !re_unfold_pos_concat_rec ($t) {|@re.empty|} ($ro) ($i) ↪ {|@pair|} ("") true
with !re_unfold_pos_concat_rec ($t) (re⋅++ (str⋅to_re ($s)) ($r2)) ($ro) ($i) ↪ (let res ≔ !re_unfold_pos_concat_rec ($t) ($r2) ($ro) (eo⋅⋅add ($i) (1)) in (let c ≔ !pair_first res in (let M ≔ !pair_second res in {|@pair|} (eo⋅⋅cons str⋅++ ($s) c) M)))
with !re_unfold_pos_concat_rec ($t) (re⋅++ ($r1) ($r2)) ($ro) ($i) ↪ (let res ≔ !re_unfold_pos_concat_rec ($t) ($r2) ($ro) (eo⋅⋅add ($i) (1)) in (let c ≔ !pair_first res in (let M ≔ !pair_second res in (let k ≔ {|@re_unfold_pos_component|} ($t) ($ro) ($i) in {|@pair|} (eo⋅⋅cons str⋅++ k c) (eo⋅⋅cons and (str⋅in_re k ($r1)) M)))));
symbol !re_unfold_pos_concat (t : τ String) (r : τ RegLan)≔ !re_unfold_pos_concat_rec t r r (0);
symbol !str_check_length_one (s : τ String)≔ eo⋅⋅is_eq (eo⋅⋅len s) (1);
symbol !str_check_len_gt_one (s : τ String)≔ eo⋅⋅is_eq (eo⋅⋅is_neg (eo⋅⋅add (1) (eo⋅⋅neg (eo⋅⋅len s)))) true;
sequential symbol !str_flatten_word [U : Set]: τ ((Seq U) ⤳ Seq U);
rule !str_flatten_word ("") ↪ ""
with !str_flatten_word ($t) ↪ !str_cons (eo⋅⋅extract ($t) (0) (0)) (!str_flatten_word (eo⋅⋅extract ($t) (1) (eo⋅⋅len ($t))));
sequential symbol !str_flatten [U : Set]: τ ((Seq U) ⤳ Seq U);
rule !str_flatten (str⋅++ ($t) ($tail)) ↪ eo⋅⋅ite (!str_check_len_gt_one ($t)) (!str_concat (!str_flatten_word ($t)) (!str_flatten ($tail))) (!str_cons ($t) (!str_flatten ($tail)))
with !str_flatten ($t) ↪ !str_self_if_empty ($t);
sequential symbol !str_collect_acc [U : Set]: τ ((Seq U) ⤳ {|@Pair|} (Seq U) (Seq U));
rule !str_collect_acc (str⋅++ ($t) ($tail)) ↪ eo⋅⋅ite (!str_check_length_one ($t)) ((let res ≔ !str_collect_acc ($tail) in (let s1 ≔ !pair_first res in (let s2 ≔ !pair_second res in eo⋅⋅ite (eo⋅⋅eq s1 ("")) ({|@pair|} ($t) s2) ({|@pair|} (eo⋅⋅concat ($t) s1) s2))))) ({|@pair|} ("") (str⋅++ ($t) ($tail)))
with !str_collect_acc ("") ↪ {|@pair|} ("") ("");
sequential symbol !str_collect [U : Set]: τ ((Seq U) ⤳ Seq U);
rule !str_collect (str⋅++ ($t) ($s)) ↪ (let res ≔ !str_collect_acc (str⋅++ ($t) ($s)) in (let s1 ≔ !pair_first res in (let s2 ≔ !pair_second res in eo⋅⋅ite (eo⋅⋅eq s1 ("")) (!str_cons ($t) (!str_collect ($s))) (!str_cons s1 (!str_collect s2)))))
with !str_collect ($t) ↪ !str_self_if_empty ($t);
sequential symbol !str_strip_prefix [U : Set]: τ ((Seq U) ⤳ (Seq U) ⤳ {|@Pair|} (Seq U) (Seq U));
rule !str_strip_prefix (str⋅++ ($t) ($t2)) (str⋅++ ($t) ($s2)) ↪ !str_strip_prefix ($t2) ($s2)
with !str_strip_prefix ($t) ($s) ↪ {|@pair|} ($t) ($s);
sequential symbol !str_mk_re_loop_elim_rec : τ (Int ⤳ Int ⤳ RegLan ⤳ RegLan ⤳ RegLan);
rule !str_mk_re_loop_elim_rec (0) (0) ($r) ($rr) ↪ eo⋅⋅cons re⋅union (eo⋅⋅list_singleton_elim re⋅++ ($rr)) re⋅none
with !str_mk_re_loop_elim_rec (0) ($d) ($r) ($rr) ↪ eo⋅⋅cons re⋅union (eo⋅⋅list_singleton_elim re⋅++ ($rr)) (!str_mk_re_loop_elim_rec (0) (eo⋅⋅add ($d) (-1)) ($r) (re⋅++ ($r) ($rr)))
with !str_mk_re_loop_elim_rec ($n) ($d) ($r) ($rr) ↪ !str_mk_re_loop_elim_rec (eo⋅⋅add ($n) (-1)) ($d) ($r) (re⋅++ ($r) ($rr));
symbol !str_mk_re_loop_elim (n : τ Int) (d : τ Int) (r : τ RegLan)≔ eo⋅⋅list_singleton_elim re⋅union (!str_mk_re_loop_elim_rec n d r {|@re.empty|});
sequential symbol !str_mk_str_in_re_concat_star_char : τ (String ⤳ RegLan ⤳ Bool);
rule !str_mk_str_in_re_concat_star_char (str⋅++ ($s1) ($s2)) ($r) ↪ eo⋅⋅cons and (str⋅in_re ($s1) ($r)) (!str_mk_str_in_re_concat_star_char ($s2) ($r))
with !str_mk_str_in_re_concat_star_char ("") ($r) ↪ true;
sequential symbol !str_mk_str_in_re_sigma_rec : τ (String ⤳ RegLan ⤳ Int ⤳ Bool ⤳ Bool);
rule !str_mk_str_in_re_sigma_rec ($s) {|@re.empty|} ($n) ($b) ↪ eo⋅⋅ite ($b) (and (= (str⋅len ($s)) ($n))) (and (>= (str⋅len ($s)) ($n)))
with !str_mk_str_in_re_sigma_rec ($s) (re⋅++ re⋅allchar ($r)) ($n) ($b) ↪ !str_mk_str_in_re_sigma_rec ($s) ($r) (eo⋅⋅add ($n) (1)) ($b)
with !str_mk_str_in_re_sigma_rec ($s) (re⋅++ (re⋅* re⋅allchar) ($r)) ($n) ($b) ↪ !str_mk_str_in_re_sigma_rec ($s) ($r) ($n) false;
symbol !str_mk_str_in_re_sigma (s : τ String) (r : τ RegLan)≔ !str_mk_str_in_re_sigma_rec s r (0) true;
sequential symbol !str_mk_str_in_re_sigma_star_rec : τ (String ⤳ RegLan ⤳ Int ⤳ Bool);
rule !str_mk_str_in_re_sigma_star_rec ($s) {|@re.empty|} ($n) ↪ and (= (mod (str⋅len ($s)) ($n)) (0))
with !str_mk_str_in_re_sigma_star_rec ($s) (re⋅++ re⋅allchar ($r)) ($n) ↪ !str_mk_str_in_re_sigma_star_rec ($s) ($r) (eo⋅⋅add ($n) (1));
symbol !str_mk_str_in_re_sigma_star (s : τ String) (r : τ RegLan)≔ !str_mk_str_in_re_sigma_star_rec s r (0);
symbol !str_to_flat_form [U : Set] (s : τ (Seq U)) (rev : τ Bool)≔ !str_rev rev (!str_flatten (!str_nary_intro s));
symbol !str_to_nary_form [U : Set] (s : τ (Seq U)) (rev : τ Bool)≔ !str_rev rev (!str_nary_intro s);
sequential symbol !re_str_to_flat_form : τ (Bool ⤳ RegLan ⤳ RegLan);
rule !re_str_to_flat_form ($rev) (re⋅++ (str⋅to_re ($s)) ($r2)) ↪ eo⋅⋅cons re⋅++ (str⋅to_re (!str_to_flat_form ($s) ($rev))) (!re_str_to_flat_form ($rev) ($r2))
with !re_str_to_flat_form ($rev) (re⋅++ ($r1) ($r2)) ↪ eo⋅⋅cons re⋅++ ($r1) (!re_str_to_flat_form ($rev) ($r2))
with !re_str_to_flat_form ($rev) ($r1) ↪ $r1;
symbol !re_to_flat_form (r : τ RegLan) (rev : τ Bool)≔ !re_str_to_flat_form rev (!str_re_rev rev (!re_nary_intro r));
symbol !str_from_flat_form [U : Set] (s : τ (Seq U)) (rev : τ Bool)≔ !str_nary_elim (!str_collect (!str_rev rev s));
symbol !str_from_nary_form [U : Set] (s : τ (Seq U)) (rev : τ Bool)≔ !str_nary_elim (!str_rev rev s);
sequential symbol !re_str_from_flat_form : τ (Bool ⤳ RegLan ⤳ RegLan);
rule !re_str_from_flat_form ($rev) (re⋅++ (str⋅to_re ($s)) ($r2)) ↪ eo⋅⋅cons re⋅++ (str⋅to_re (!str_from_flat_form ($s) ($rev))) (!re_str_from_flat_form ($rev) ($r2))
with !re_str_from_flat_form ($rev) (re⋅++ ($r1) ($r2)) ↪ eo⋅⋅cons re⋅++ ($r1) (!re_str_from_flat_form ($rev) ($r2))
with !re_str_from_flat_form ($rev) ($r1) ↪ $r1;
symbol !re_from_flat_form (r : τ RegLan) (rev : τ Bool)≔ !re_nary_elim (!str_re_rev rev (!re_str_from_flat_form rev r));
sequential symbol !str_re_includes_lhs_union : τ (RegLan ⤳ RegLan ⤳ Bool);
rule !str_re_includes_lhs_union (re⋅union ($r1) ($r2)) ($r3) ↪ eo⋅⋅ite (!str_re_includes ($r1) ($r3)) true (!str_re_includes_lhs_union ($r2) ($r3))
with !str_re_includes_lhs_union ($r1) ($r3) ↪ false;
sequential symbol !str_re_includes_rhs_inter : τ (RegLan ⤳ RegLan ⤳ Bool);
rule !str_re_includes_rhs_inter ($r1) (re⋅inter ($r3) ($r2)) ↪ eo⋅⋅ite (!str_re_includes ($r1) ($r3)) true (!str_re_includes_rhs_inter ($r1) ($r2))
with !str_re_includes_rhs_inter ($r1) ($r3) ↪ false;
sequential symbol !str_maybe_get_star_body : τ (RegLan ⤳ RegLan);
rule !str_maybe_get_star_body (re⋅* ($r)) ↪ $r
with !str_maybe_get_star_body ($r) ↪ $r;
sequential symbol !str_re_includes_lhs_star : τ (RegLan ⤳ RegLan ⤳ Bool);
rule !str_re_includes_lhs_star (re⋅* ($r1)) ($r2) ↪ eo⋅⋅ite (eo⋅⋅eq ($r1) re⋅allchar) true (!str_re_includes ($r1) (!str_maybe_get_star_body ($r2)))
with !str_re_includes_lhs_star ($r1) ($r2) ↪ false;
sequential symbol !str_re_includes_is_rec : τ (RegLan ⤳ RegLan ⤳ Bool);
rule !str_re_includes_is_rec ($r1) (re⋅inter ($r3) ($r2)) ↪ false
with !str_re_includes_is_rec (re⋅union ($r1) ($r2)) ($r3) ↪ false
with !str_re_includes_is_rec (re⋅* ($r1)) ($r3) ↪ false
with !str_re_includes_is_rec (re⋅++ ($r1) ($r2)) ($r3) ↪ true
with !str_re_includes_is_rec ($r3) (re⋅++ ($r1) ($r2)) ↪ true
with !str_re_includes_is_rec ($r1) ($r3) ↪ false;
sequential symbol !re_is_unbound_wildcard : τ (RegLan ⤳ Bool);
rule !re_is_unbound_wildcard (re⋅++ (re⋅* re⋅allchar) ($r2)) ↪ true
with !re_is_unbound_wildcard (re⋅++ re⋅allchar ($r2)) ↪ !re_is_unbound_wildcard ($r2)
with !re_is_unbound_wildcard ($r1) ↪ false;
sequential symbol !str_re_includes_rec : τ (RegLan ⤳ RegLan ⤳ Bool);
rule !str_re_includes_rec ($r1) ($r1) ↪ true
with !str_re_includes_rec (re⋅++ (str⋅to_re (str⋅++ ($s1) ($s2))) ($r2)) ($r3) ↪ !str_re_includes_rec (re⋅++ (str⋅to_re ($s1)) (re⋅++ (str⋅to_re ($s2)) (eo⋅⋅list_concat re⋅++ ($r2) {|@re.empty|}))) ($r3)
with !str_re_includes_rec (re⋅++ (str⋅to_re ("")) ($r2)) ($r3) ↪ !str_re_includes_rec ($r2) ($r3)
with !str_re_includes_rec ($r1) (re⋅++ (str⋅to_re (str⋅++ ($s1) ($s2))) ($r4)) ↪ !str_re_includes_rec ($r1) (re⋅++ (str⋅to_re ($s1)) (re⋅++ (str⋅to_re ($s2)) (eo⋅⋅list_concat re⋅++ ($r4) {|@re.empty|})))
with !str_re_includes_rec ($r1) (re⋅++ (str⋅to_re ("")) ($r4)) ↪ !str_re_includes_rec ($r1) ($r4)
with !str_re_includes_rec (re⋅++ ($r1) ($r2)) (re⋅++ ($r3) ($r4)) ↪ eo⋅⋅ite (eo⋅⋅ite (!str_re_includes (!re_from_flat_form ($r1) false) (!re_from_flat_form ($r3) false)) (!str_re_includes_rec ($r2) ($r4)) false) true (eo⋅⋅ite (eo⋅⋅ite (!re_is_unbound_wildcard (re⋅++ ($r1) ($r2))) (!str_re_includes_rec (re⋅++ ($r1) ($r2)) ($r4)) false) true (eo⋅⋅ite (eo⋅⋅ite (eo⋅⋅eq ($r1) (re⋅* re⋅allchar)) (!str_re_includes_rec ($r2) (re⋅++ ($r3) ($r4))) false) true false))
with !str_re_includes_rec (re⋅++ ($r1) ($r2)) {|@re.empty|} ↪ eo⋅⋅and (eo⋅⋅eq ($r1) (re⋅* re⋅allchar)) (eo⋅⋅eq ($r2) {|@re.empty|})
with !str_re_includes_rec ($r1) ($r3) ↪ false;
sequential symbol !str_re_includes : τ (RegLan ⤳ RegLan ⤳ Bool);
rule !str_re_includes ($r1) ($r1) ↪ true
with !str_re_includes ($r1) (str⋅to_re ($s1)) ↪ !str_eval_str_in_re ($s1) ($r1)
with !str_re_includes (str⋅to_re ($s1)) ($r1) ↪ false
with !str_re_includes (re⋅range ($s1) ($s2)) (re⋅range ($s3) ($s4)) ↪ (let z1 ≔ eo⋅⋅to_z ($s1) in (let z2 ≔ eo⋅⋅to_z ($s2) in (let z3 ≔ eo⋅⋅to_z ($s3) in (let z4 ≔ eo⋅⋅to_z ($s4) in eo⋅⋅requires (eo⋅⋅is_neg z1) false (eo⋅⋅requires (eo⋅⋅is_neg z2) false (eo⋅⋅requires (eo⋅⋅is_neg z3) false (eo⋅⋅requires (eo⋅⋅is_neg z4) false (eo⋅⋅and (!compare_geq z2 z3) (!compare_geq z3 z1) (!compare_geq z2 z4) (!compare_geq z4 z1)))))))))
with !str_re_includes ($r1) ($r3) ↪ eo⋅⋅ite (eo⋅⋅eq (!str_re_includes_lhs_union ($r1) ($r3)) true) true (eo⋅⋅ite (eo⋅⋅eq (!str_re_includes_rhs_inter ($r1) ($r3)) true) true (eo⋅⋅ite (eo⋅⋅eq (!str_re_includes_lhs_star ($r1) ($r3)) true) true (eo⋅⋅ite (!str_re_includes_is_rec ($r1) ($r3)) (!str_re_includes_rec (!re_to_flat_form ($r1) false) (!re_to_flat_form ($r3) false)) false)));
sequential symbol !str_arith_entail_simple [T : Set]: τ (T ⤳ Bool);
rule !str_arith_entail_simple (str⋅len ($s)) ↪ true
with !str_arith_entail_simple (+ ($n1) ($n2)) ↪ eo⋅⋅ite (!str_arith_entail_simple ($n1)) (!str_arith_entail_simple ($n2)) false
with !str_arith_entail_simple (* ($n1) ($n2)) ↪ eo⋅⋅ite (!str_arith_entail_simple ($n1)) (!str_arith_entail_simple ($n2)) false
with !str_arith_entail_simple ($n1) ↪ eo⋅⋅not (eo⋅⋅is_neg ($n1));
sequential symbol !str_arith_entail_simple_pred : τ (Bool ⤳ Bool);
rule !str_arith_entail_simple_pred (and (>= ($n) ($m))) ↪ !str_arith_entail_simple (!arith_poly_to_term (- ($n) ($m)))
with !str_arith_entail_simple_pred (and (> ($n) ($m))) ↪ !str_arith_entail_simple (!arith_poly_to_term (- ($n) (+ ($m) (+ (1) (0)))));
sequential symbol !str_arith_entail_is_approx_len : τ (String ⤳ Int ⤳ Bool ⤳ Bool);
rule !str_arith_entail_is_approx_len (str⋅substr ($s) ($n1) ($n2)) ($n) ($isUnder) ↪ (let npm ≔ + ($n1) (+ ($n2) (0)) in (let lx ≔ str⋅len ($s) in eo⋅⋅ite (eo⋅⋅eq ($n) ($n2)) (eo⋅⋅ite ($isUnder) (eo⋅⋅and (!str_arith_entail_simple ($n1)) (!str_arith_entail_simple_pred (and (>= lx npm)))) (!str_arith_entail_simple ($n2))) (eo⋅⋅ite (eo⋅⋅eq ($n) lx) (eo⋅⋅not ($isUnder)) (eo⋅⋅ite (eo⋅⋅eq ($n) (- lx ($n1))) (eo⋅⋅ite ($isUnder) (eo⋅⋅and (!str_arith_entail_simple ($n1)) (!str_arith_entail_simple_pred (and (>= npm lx)))) (!str_arith_entail_simple_pred (and (>= lx ($n1))))) false))))
with !str_arith_entail_is_approx_len (str⋅replace ($s) ($t) ($r)) ($n) ($isUnder) ↪ (let ls ≔ str⋅len ($s) in (let lt ≔ str⋅len ($t) in (let lr ≔ str⋅len ($r) in eo⋅⋅ite (eo⋅⋅eq ($n) ls) (eo⋅⋅ite ($isUnder) (eo⋅⋅or (!str_arith_entail_simple_pred (and (>= lr lt))) (!str_arith_entail_simple_pred (and (>= lr ls)))) (!str_arith_entail_simple_pred (and (>= lt lr)))) (eo⋅⋅ite (eo⋅⋅eq ($n) (+ ls (+ lr (0)))) (eo⋅⋅not ($isUnder)) (eo⋅⋅ite (eo⋅⋅eq ($n) (- ls lt)) ($isUnder) false)))))
with !str_arith_entail_is_approx_len (str⋅from_int ($n1)) ($n) ($isUnder) ↪ eo⋅⋅ite (eo⋅⋅eq ($n) (+ ($n1) (+ (1) (0)))) (eo⋅⋅and (eo⋅⋅not ($isUnder)) (!str_arith_entail_simple ($n1))) (eo⋅⋅ite (eo⋅⋅eq ($n) ($n1)) (eo⋅⋅and (eo⋅⋅not ($isUnder)) (!str_arith_entail_simple_pred (and (> ($n1) (0))))) (eo⋅⋅ite (eo⋅⋅eq ($n) (1)) (eo⋅⋅and ($isUnder) (!str_arith_entail_simple ($n1))) false));
symbol !str_arith_entail_is_approx_indexof (s : τ String) (t : τ String) (n : τ Int) (m : τ Int) (isUnder : τ Bool)≔ (let ls ≔ str⋅len s in (let lt ≔ str⋅len t in eo⋅⋅ite (eo⋅⋅eq m (-1)) isUnder (eo⋅⋅ite (eo⋅⋅eq m ls) (eo⋅⋅not isUnder) (eo⋅⋅ite (eo⋅⋅eq m (- ls lt)) (eo⋅⋅and (eo⋅⋅not isUnder) (!str_arith_entail_simple_pred (and (>= ls lt)))) false))));
symbol !str_arith_entail_is_approx_to_int (s : τ String) (n : τ Int) (isUnder : τ Bool)≔ eo⋅⋅ite (eo⋅⋅eq n (-1)) isUnder false;
sequential symbol !str_arith_entail_is_approx : τ (Int ⤳ Int ⤳ Bool ⤳ Bool);
rule !str_arith_entail_is_approx ($n1) ($n1) ($isUnder) ↪ true
with !str_arith_entail_is_approx (str⋅len ($s)) ($n1) ($isUnder) ↪ !str_arith_entail_is_approx_len ($s) ($n1) ($isUnder)
with !str_arith_entail_is_approx (str⋅indexof ($s) ($t) ($n3)) ($n1) ($isUnder) ↪ !str_arith_entail_is_approx_indexof ($s) ($t) ($n3) ($n1) ($isUnder)
with !str_arith_entail_is_approx (str⋅to_int ($s)) ($n1) ($isUnder) ↪ !str_arith_entail_is_approx_to_int ($s) ($n1) ($isUnder)
with !str_arith_entail_is_approx (+ ($n1) ($n2)) (+ ($n3) ($n4)) ($isUnder) ↪ eo⋅⋅and (!str_arith_entail_is_approx ($n1) ($n3) ($isUnder)) (!str_arith_entail_is_approx ($n2) ($n4) ($isUnder))
with !str_arith_entail_is_approx (* ($n1) (* ($n3) (1))) (* ($n1) (* ($n5) (1))) ($isUnder) ↪ eo⋅⋅ite (eo⋅⋅is_neg ($n1)) (!str_arith_entail_is_approx ($n3) ($n5) (eo⋅⋅not ($isUnder))) (!str_arith_entail_is_approx ($n3) ($n5) ($isUnder));
sequential symbol !str_re_consume_rec : τ (String ⤳ RegLan ⤳ Bool ⤳ Bool ⤳ Bool);
rule !str_re_consume_rec (str⋅++ ($s1) ($s2)) (re⋅++ (str⋅to_re (str⋅++ ($s3) ($s4))) ($r2)) {|@result.null|} ($rev) ↪ eo⋅⋅ite (eo⋅⋅eq ($s1) ($s3)) (!str_re_consume_rec ($s2) (re⋅++ (str⋅to_re ($s4)) ($r2)) {|@result.null|} ($rev)) (eo⋅⋅ite (eo⋅⋅and (!str_check_length_one ($s1)) (!str_check_length_one ($s3))) false (str⋅in_re (str⋅++ ($s1) ($s2)) (re⋅++ (str⋅to_re (str⋅++ ($s3) ($s4))) ($r2))))
with !str_re_consume_rec (str⋅++ ($s1) ($s2)) (re⋅++ {|@re.empty|} ($r2)) {|@result.null|} ($rev) ↪ !str_re_consume_rec (str⋅++ ($s1) ($s2)) ($r2) {|@result.null|} ($rev)
with !str_re_consume_rec (str⋅++ ($s1) ($s2)) (re⋅++ (re⋅range ($s3) ($s5)) ($r2)) {|@result.null|} ($rev) ↪ eo⋅⋅ite (eo⋅⋅and (!str_check_length_one ($s1)) (!str_is_char_range ($s3) ($s5))) (eo⋅⋅ite (!str_eval_str_in_re ($s1) (re⋅range ($s3) ($s5))) (!str_re_consume_rec ($s2) ($r2) {|@result.null|} ($rev)) false) (str⋅in_re (str⋅++ ($s1) ($s2)) (re⋅++ (re⋅range ($s3) ($s5)) ($r2)))
with !str_re_consume_rec (str⋅++ ($s1) ($s2)) (re⋅++ re⋅allchar ($r2)) {|@result.null|} ($rev) ↪ eo⋅⋅ite (!str_check_length_one ($s1)) (!str_re_consume_rec ($s2) ($r2) {|@result.null|} ($rev)) (str⋅in_re (str⋅++ ($s1) ($s2)) (re⋅++ re⋅allchar ($r2)))
with !str_re_consume_rec (str⋅++ ($s1) ($s2)) (re⋅++ (re⋅* ($r3)) ($r2)) {|@result.null|} ($rev) ↪ (let r1 ≔ re⋅* ($r3) in (let res ≔ !str_re_consume_rec (str⋅++ ($s1) ($s2)) (!re_to_flat_form ($r3) ($rev)) {|@result.null|} ($rev) in eo⋅⋅ite (eo⋅⋅eq res false) (!str_re_consume_rec (str⋅++ ($s1) ($s2)) ($r2) {|@result.null|} ($rev)) (eo⋅⋅ite (eo⋅⋅eq (!str_membership_re res) {|@re.empty|}) ((let res2 ≔ !str_re_consume_rec (str⋅++ ($s1) ($s2)) ($r2) {|@result.null|} ($rev) in eo⋅⋅ite (eo⋅⋅is_eq res2 false) ((let sr ≔ !str_membership_str res in eo⋅⋅ite (eo⋅⋅eq (str⋅++ ($s1) ($s2)) sr) (str⋅in_re (str⋅++ ($s1) ($s2)) (re⋅++ ($r1) ($r2))) (!str_re_consume_rec sr (re⋅++ ($r1) ($r2)) {|@result.null|} ($rev)))) (str⋅in_re (str⋅++ ($s1) ($s2)) (re⋅++ ($r1) ($r2))))) (str⋅in_re (str⋅++ ($s1) ($s2)) (re⋅++ ($r1) ($r2))))))
with !str_re_consume_rec (str⋅++ ($s1) ($s2)) (re⋅++ ($r1) ($r2)) {|@result.null|} ($rev) ↪ (let res ≔ !str_re_consume_rec (str⋅++ ($s1) ($s2)) ($r1) {|@result.null|} ($rev) in eo⋅⋅ite (eo⋅⋅is_eq res false) false (eo⋅⋅ite (eo⋅⋅is_eq (!str_membership_re res) {|@re.empty|}) (!str_re_consume_rec (!str_membership_str res) ($r2) {|@result.null|} ($rev)) (str⋅in_re (str⋅++ ($s1) ($s2)) (re⋅++ ($r1) ($r2)))))
with !str_re_consume_rec ($s1) (re⋅++ {|@re.empty|} ($r2)) {|@result.null|} ($rev) ↪ !str_re_consume_rec ($s1) ($r2) {|@result.null|} ($rev)
with !str_re_consume_rec ($s1) (re⋅inter ($r1) ($r2)) ($b) ($rev) ↪ (let r1r ≔ !re_to_flat_form ($r1) ($rev) in (let bb ≔ !str_re_consume_rec ($s1) r1r {|@result.null|} ($rev) in eo⋅⋅ite (eo⋅⋅eq bb false) false (!str_re_consume_rec ($s1) ($r2) (!result_combine bb ($b)) ($rev))))
with !str_re_consume_rec ($s1) re⋅all {|@result.null|} ($rev) ↪ str⋅in_re ("") {|@re.empty|}
with !str_re_consume_rec ($s1) re⋅all ($b) ($rev) ↪ $b
with !str_re_consume_rec ($s1) (re⋅union ($r1) ($r2)) ($b) ($rev) ↪ (let r1r ≔ !re_to_flat_form ($r1) ($rev) in (let bb ≔ !str_re_consume_rec ($s1) r1r {|@result.null|} ($rev) in eo⋅⋅ite (eo⋅⋅eq bb false) (!str_re_consume_rec ($s1) ($r2) ($b) ($rev)) (!str_re_consume_rec ($s1) ($r2) (!result_combine bb ($b)) ($rev))))
with !str_re_consume_rec ($s1) re⋅none {|@result.null|} ($rev) ↪ false
with !str_re_consume_rec ($s1) re⋅none ($b) ($rev) ↪ $b
with !str_re_consume_rec ($s1) ($r1) {|@result.null|} ($rev) ↪ str⋅in_re ($s1) ($r1);
symbol !str_re_consume_process (s : τ String) (r : τ RegLan) (oneDir : τ Bool)≔ (let ss ≔ !str_to_flat_form s true in (let rr ≔ !re_to_flat_form r true in (let resrev ≔ !str_re_consume_rec ss rr {|@result.null|} true in eo⋅⋅ite (eo⋅⋅eq resrev false) false ((let s1 ≔ !str_membership_str resrev in (let r1 ≔ !str_membership_re resrev in (let revert ≔ eo⋅⋅and oneDir (eo⋅⋅not (eo⋅⋅eq r1 {|@re.empty|})) in (let s1r ≔ !str_rev true (eo⋅⋅ite revert ss s1) in (let r1r ≔ !re_to_flat_form (eo⋅⋅ite revert rr r1) true in (let resfwd ≔ !str_re_consume_rec s1r r1r {|@result.null|} false in eo⋅⋅ite (eo⋅⋅eq resfwd false) false ((let s2 ≔ !str_membership_str resfwd in (let r2 ≔ !str_membership_re resfwd in str⋅in_re (!str_from_flat_form s2 false) (!re_from_flat_form r2 false))))))))))))));
sequential symbol !str_re_consume : τ (String ⤳ RegLan ⤳ Bool);
rule !str_re_consume ($s) (re⋅* ($r)) ↪ (let res ≔ !str_re_consume_process ($s) ($r) true in eo⋅⋅ite (eo⋅⋅eq res false) false (eo⋅⋅requires (!str_membership_re res) {|@re.empty|} (str⋅in_re (!str_membership_str res) (re⋅* ($r)))))
with !str_re_consume ($s) ($r) ↪ !str_re_consume_process ($s) ($r) false;
sequential symbol !str_is_compatible [T : Set]: τ ((Seq T) ⤳ (Seq T) ⤳ Bool);
rule !str_is_compatible (str⋅++ ($c1) ($xs1)) (str⋅++ ($c1) ($xs2)) ↪ !str_is_compatible ($xs1) ($xs2)
with !str_is_compatible (str⋅++ ($c1) ($xs1)) (str⋅++ ($c2) ($xs2)) ↪ eo⋅⋅requires (!are_distinct_terms ($c1) ($c2)) true false
with !str_is_compatible ($c1) ($c2) ↪ eo⋅⋅or (!str_is_empty ($c1)) (!str_is_empty ($c2));
sequential symbol !str_overlap_rec : τ (String ⤳ String ⤳ Int);
rule !str_overlap_rec (str⋅++ ($s) ($s1)) ($t) ↪ eo⋅⋅ite (!str_is_compatible (str⋅++ ($s) ($s1)) ($t)) (0) (eo⋅⋅add (1) (!str_overlap_rec ($s1) ($t)))
with !str_overlap_rec ($s) ($t) ↪ 0;
symbol !str_overlap [U : Set] (s : τ (Seq U)) (t : τ (Seq U)) (rev : τ Bool)≔ !str_overlap_rec (!str_to_flat_form s rev) (!str_to_flat_form t rev);
symbol !str_has_overlap [U : Set] (s : τ (Seq U)) (t : τ (Seq U)) (rev : τ Bool)≔ eo⋅⋅gt (!str_value_len s) (!str_overlap s t rev);
sequential symbol !str_from_int_eval_rec : τ (Int ⤳ String ⤳ String);
rule !str_from_int_eval_rec ($n) ($s) ↪ eo⋅⋅ite (eo⋅⋅eq ($n) (0)) (eo⋅⋅ite (eo⋅⋅eq ($s) ("")) ("0") ($s)) (!str_from_int_eval_rec (eo⋅⋅zdiv ($n) (10)) (eo⋅⋅concat (eo⋅⋅to_str (eo⋅⋅add (48) (eo⋅⋅zmod ($n) (10)))) ($s)));
symbol !str_from_int_eval (n : τ Int)≔ eo⋅⋅ite (eo⋅⋅is_z n) (eo⋅⋅ite (eo⋅⋅is_neg n) ("") (!str_from_int_eval_rec n (""))) (str⋅from_int n);
sequential symbol !str_to_int_eval_rec : τ (String ⤳ Int ⤳ Int ⤳ Int);
rule !str_to_int_eval_rec (str⋅++ ($s1) ($s2)) ($e) ($n) ↪ (let c ≔ eo⋅⋅add (eo⋅⋅to_z ($s1)) (-48) in eo⋅⋅ite (eo⋅⋅and (eo⋅⋅gt (10) c) (eo⋅⋅not (eo⋅⋅is_neg c))) (!str_to_int_eval_rec ($s2) (eo⋅⋅mul ($e) (10)) (eo⋅⋅add (eo⋅⋅mul c ($e)) ($n))) (-1))
with !str_to_int_eval_rec ("") ($e) ($n) ↪ $n;
symbol !str_to_int_eval (s : τ String)≔ eo⋅⋅ite (eo⋅⋅is_str s) (eo⋅⋅ite (eo⋅⋅eq s ("")) (-1) (!str_to_int_eval_rec (!str_to_flat_form s true) (1) (0))) (str⋅to_int s);
sequential symbol !str_case_conv_rec : τ (String ⤳ Bool ⤳ String);
rule !str_case_conv_rec (str⋅++ ($s1) ($s2)) true ↪ (let c ≔ eo⋅⋅to_z ($s1) in eo⋅⋅concat (eo⋅⋅to_str (eo⋅⋅add c (eo⋅⋅ite (eo⋅⋅and (eo⋅⋅gt (91) c) (eo⋅⋅gt c (64))) (32) (0)))) (!str_case_conv_rec ($s2) true))
with !str_case_conv_rec (str⋅++ ($s1) ($s2)) false ↪ (let c ≔ eo⋅⋅to_z ($s1) in eo⋅⋅concat (eo⋅⋅to_str (eo⋅⋅add c (eo⋅⋅ite (eo⋅⋅and (eo⋅⋅gt (123) c) (eo⋅⋅gt c (96))) (-32) (0)))) (!str_case_conv_rec ($s2) false))
with !str_case_conv_rec ("") ($isLower) ↪ "";
symbol !str_to_lower_eval (s : τ String)≔ eo⋅⋅ite (eo⋅⋅is_str s) (!str_case_conv_rec (!str_to_flat_form s false) true) (str⋅to_lower s);
symbol !str_to_upper_eval (s : τ String)≔ eo⋅⋅ite (eo⋅⋅is_str s) (!str_case_conv_rec (!str_to_flat_form s false) false) (str⋅to_upper s);
symbol !str_rev_eval (s : τ String)≔ eo⋅⋅ite (eo⋅⋅is_str s) (!str_from_flat_form (!str_to_flat_form s true) false) (str⋅rev s);
sequential symbol !str_leq_eval_rec : τ (String ⤳ String ⤳ Bool);
rule !str_leq_eval_rec (str⋅++ ($s1) ($s2)) (str⋅++ ($t1) ($t2)) ↪ eo⋅⋅ite (eo⋅⋅eq ($s1) ($t1)) (!str_leq_eval_rec ($s2) ($t2)) (eo⋅⋅gt (eo⋅⋅to_z ($t1)) (eo⋅⋅to_z ($s1)))
with !str_leq_eval_rec ("") ($t1) ↪ true
with !str_leq_eval_rec ($s1) ($t1) ↪ false;
symbol !str_leq_eval (s : τ String) (t : τ String)≔ eo⋅⋅ite (eo⋅⋅and (eo⋅⋅is_str s) (eo⋅⋅is_str t)) (!str_leq_eval_rec (!str_to_flat_form s false) (!str_to_flat_form t false)) (str⋅<= s t);
sequential symbol !str_eval_replace_all_rec : τ (String ⤳ String ⤳ String ⤳ Int ⤳ Int ⤳ String);
rule !str_eval_replace_all_rec ($s) ($t) ($u) (-1) ($lent) ↪ $s
with !str_eval_replace_all_rec ($s) ($t) ($u) ($n) ($lent) ↪ (let snext ≔ eo⋅⋅extract ($s) (eo⋅⋅add ($n) ($lent)) (eo⋅⋅len ($s)) in eo⋅⋅concat (eo⋅⋅extract ($s) (0) (eo⋅⋅add ($n) (-1))) ($u) (!str_eval_replace_all_rec snext ($t) ($u) (eo⋅⋅find snext ($t)) ($lent)));
symbol !str_eval_replace_all (s : τ String) (t : τ String) (u : τ String)≔ eo⋅⋅ite (eo⋅⋅and (eo⋅⋅is_str s) (eo⋅⋅is_str t) (eo⋅⋅is_str u)) (eo⋅⋅ite (eo⋅⋅eq t ("")) s (!str_eval_replace_all_rec s t u (eo⋅⋅find s t) (eo⋅⋅len t))) (str⋅replace_all s t u);
