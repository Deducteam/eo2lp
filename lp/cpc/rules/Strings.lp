require open cpc.Core Stdlib.Set cpc.theories.Strings cpc.theories.Quantifiers cpc.programs.Quantifiers cpc.programs.Strings cpc.programs.DistinctValues;
sequential symbol !mk_re_concat : τ (Bool ⤳ Bool ⤳ Bool);
rule !mk_re_concat (and (str⋅in_re ($s) ($r)) ($Es)) (str⋅in_re ($s1) ($r1)) ↪ !mk_re_concat ($Es) (str⋅in_re (eo⋅⋅cons str⋅++ ($s) ($s1)) (eo⋅⋅cons re⋅++ ($r) ($r1)))
with !mk_re_concat true (str⋅in_re ($s1) ($r1)) ↪ str⋅in_re ($s1) ($r1);
sequential symbol !mk_re_unfold_pos_star : τ (String ⤳ RegLan ⤳ ({|@Pair|} String Bool) ⤳ Bool);
rule !mk_re_unfold_pos_star ($t) ($r) ({|@pair|} (str⋅++ ($k1) (str⋅++ ($k2) (str⋅++ ($k3) (!seq_empty (Seq T))))) ($M)) ↪ or (and (= ($t) (""))) (str⋅in_re ($t) ($r)) (and (and (and (= ($t) (str⋅++ ($k1) (str⋅++ ($k2) (str⋅++ ($k3) (!seq_empty (Seq T))))))) ($M)) (not (and (= ($k1) ("")))) (not (and (= ($k3) ("")))));
sequential symbol !mk_re_unfold_pos : τ (String ⤳ RegLan ⤳ Bool);
rule !mk_re_unfold_pos ($t) (re⋅* ($r1)) ↪ !mk_re_unfold_pos_star ($t) ($r1) (!re_unfold_pos_concat ($t) (re⋅++ ($r1) (re⋅++ (re⋅* ($r1)) (re⋅++ ($r1) {|@re.empty|}))))
with !mk_re_unfold_pos ($t) (re⋅++ ($r1) ($r2)) ↪ (let res ≔ !re_unfold_pos_concat ($t) (re⋅++ ($r1) ($r2)) in (let teq ≔ and (= ($t) (!pair_first res)) in (let M ≔ !pair_second res in eo⋅⋅ite (eo⋅⋅eq M true) teq (eo⋅⋅cons and teq M))));
sequential symbol !mk_re_unfold_neg_concat_fixed : τ (String ⤳ RegLan ⤳ Bool ⤳ Bool);
rule !mk_re_unfold_neg_concat_fixed ($s) (re⋅++ ($r1) ($r2)) ($rev) ↪ (let n ≔ !str_fixed_len_re ($r1) in eo⋅⋅ite ($rev) (or (not (str⋅in_re (!str_suffix ($s) n) ($r1))) (not (str⋅in_re (!str_prefix ($s) (- (str⋅len ($s)) n)) (eo⋅⋅list_singleton_elim re⋅++ (!str_re_rev ($rev) ($r2)))))) (or (not (str⋅in_re (!str_prefix ($s) n) ($r1))) (not (str⋅in_re (!str_suffix_rem ($s) n) (eo⋅⋅list_singleton_elim re⋅++ ($r2))))));
sequential symbol !mk_re_unfold_neg : τ (String ⤳ RegLan ⤳ Bool);
rule !mk_re_unfold_neg ($t) (re⋅* ($r1)) ↪ and (not (and (= ($t) ("")))) (forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) (or (and (<= {|@var.str_index|} (0))) (and (< (str⋅len ($t)) {|@var.str_index|})) (not (str⋅in_re (!str_prefix ($t) {|@var.str_index|}) ($r1))) (not (str⋅in_re (!str_suffix_rem ($t) {|@var.str_index|}) (re⋅* ($r1))))))
with !mk_re_unfold_neg ($t) (re⋅++ ($r1) ($r2)) ↪ forall ({|@list|} (eo⋅⋅var ("@var.str_index") Int)) (or (and (< {|@var.str_index|} (0))) (and (< (str⋅len ($t)) {|@var.str_index|})) (not (str⋅in_re (!str_prefix ($t) {|@var.str_index|}) ($r1))) (not (str⋅in_re (!str_suffix_rem ($t) {|@var.str_index|}) (eo⋅⋅list_singleton_elim re⋅++ ($r2)))));
sequential symbol !str_mk_ext_deq [T : Set]: τ ((Seq T) ⤳ (Seq T) ⤳ Int ⤳ eo⋅⋅Type ⤳ Bool);
rule !str_mk_ext_deq ($s) ($t) ($k) String ↪ not (and (= (str⋅substr ($s) ($k) (1)) (str⋅substr ($t) ($k) (1))))
with !str_mk_ext_deq ($s) ($t) ($k) (Seq ($T)) ↪ not (and (= (seq⋅nth ($s) ($k)) (seq⋅nth ($t) ($k))));
sequential symbol !str_multiset_overapprox [T : Set]: τ ((Seq T) ⤳ {|@List|});
rule !str_multiset_overapprox (str⋅++ ($s) ($ss)) ↪ eo⋅⋅list_concat {|@list|} (!str_multiset_overapprox ($s)) (!str_multiset_overapprox ($ss))
with !str_multiset_overapprox (str⋅substr ($s) ($n) ($m)) ↪ !str_multiset_overapprox ($s)
with !str_multiset_overapprox (str⋅replace ($s) ($t) ($r)) ↪ eo⋅⋅list_concat {|@list|} (!str_multiset_overapprox ($s)) (!str_multiset_overapprox ($r))
with !str_multiset_overapprox ($s) ↪ eo⋅⋅ite (!str_is_empty ($s)) {|@list.nil|} (eo⋅⋅ite (eo⋅⋅is_str ($s)) (eo⋅⋅ite (eo⋅⋅gt (eo⋅⋅len ($s)) (1)) (!str_multiset_overapprox (!str_flatten_word ($s))) ({|@list|} ($s))) ({|@list|} ($s)));
sequential symbol !str_is_multiset_subset_strict [T : Set]: τ ((Seq T) ⤳ {|@List|} ⤳ {|@List|} ⤳ Bool);
rule !str_is_multiset_subset_strict (str⋅++ ($s) ($ss)) ($xs) ($nr) ↪ (let xsr ≔ eo⋅⋅list_erase {|@list|} ($xs) ($s) in (let nrem ≔ eo⋅⋅eq ($xs) xsr in !str_is_multiset_subset_strict ($ss) xsr (eo⋅⋅ite nrem ({|@list|} ($s) ($nr)) ($nr))))
with !str_is_multiset_subset_strict ($emp) ($xs) ({|@list|} ($s) ($nr)) ↪ eo⋅⋅ite (!are_distinct_terms_list_rec ($s) ($xs) (eo⋅⋅typeof ($s))) true (!str_is_multiset_subset_strict ($emp) ($xs) ($nr))
with !str_is_multiset_subset_strict ($emp) ($xs) ($nr) ↪ false;
symbol !str_eval_indexof_re (s : τ String) (r : τ RegLan) (n : τ Int)≔ eo⋅⋅ite (eo⋅⋅or (eo⋅⋅gt n (eo⋅⋅len s)) (eo⋅⋅is_neg n)) (-1) ((let res ≔ !str_first_match (eo⋅⋅extract s n (eo⋅⋅len s)) r in (let sp ≔ !pair_first res in eo⋅⋅ite (eo⋅⋅eq sp (-1)) (-1) (eo⋅⋅add n sp))));
sequential symbol !str_eval_replace_re : τ (String ⤳ RegLan ⤳ String ⤳ ({|@Pair|} Int Int) ⤳ String);
rule !str_eval_replace_re ($s) ($r) ($t) ({|@pair|} (-1) (-1)) ↪ $s
with !str_eval_replace_re ($s) ($r) ($t) ({|@pair|} ($sp) ($ep)) ↪ str⋅++ (eo⋅⋅extract ($s) (0) (eo⋅⋅add ($sp) (-1))) (str⋅++ ($t) (str⋅++ (eo⋅⋅extract ($s) ($ep) (eo⋅⋅len ($s))) (!seq_empty (Seq T))));
sequential symbol !str_eval_replace_re_all_rec : τ (String ⤳ RegLan ⤳ String ⤳ ({|@Pair|} Int Int) ⤳ String);
rule !str_eval_replace_re_all_rec ("") ($r) ($t) ({|@pair|} (-1) (-1)) ↪ ""
with !str_eval_replace_re_all_rec ($s) ($r) ($t) ({|@pair|} (-1) (-1)) ↪ eo⋅⋅cons str⋅++ ($s) ("")
with !str_eval_replace_re_all_rec ($s) ($r) ($t) ({|@pair|} ($sp) ($ep)) ↪ (let snext ≔ eo⋅⋅extract ($s) ($ep) (eo⋅⋅len ($s)) in eo⋅⋅cons str⋅++ (eo⋅⋅extract ($s) (0) (eo⋅⋅add ($sp) (-1))) (eo⋅⋅cons str⋅++ ($t) (!str_eval_replace_re_all_rec snext ($r) ($t) (!str_first_match snext ($r)))));
symbol !str_eval_replace_re_all (s : τ String) (r : τ RegLan) (t : τ String)≔ (let rnemp ≔ re⋅inter r (re⋅inter (re⋅comp (str⋅to_re (""))) re⋅all) in eo⋅⋅list_singleton_elim str⋅++ (!str_eval_replace_re_all_rec s rnemp t (!str_first_match s rnemp)));
sequential symbol !seq_is_prefix [T : Set]: τ ((Seq T) ⤳ (Seq T) ⤳ Bool);
rule !seq_is_prefix ($t) ($t) ↪ true
with !seq_is_prefix (seq⋅++ ($t) ($ts)) (seq⋅++ ($t) ($ss)) ↪ !seq_is_prefix ($ts) ($ss)
with !seq_is_prefix (seq⋅++ (seq⋅unit ($et)) ($ts)) (seq⋅++ (seq⋅unit ($es)) ($ss)) ↪ eo⋅⋅requires (!are_distinct_terms ($et) ($es)) true false
with !seq_is_prefix ({|as|} seq⋅empty (Seq ($T))) ($t) ↪ true
with !seq_is_prefix (seq⋅++ (seq⋅unit ($et)) ($ts)) ({|as|} seq⋅empty (Seq ($T))) ↪ false;
sequential symbol !seq_find [T : Set]: τ ((Seq T) ⤳ (Seq T) ⤳ Int ⤳ Int);
rule !seq_find ($t) ($t) ($n) ↪ $n
with !seq_find ({|as|} seq⋅empty (Seq ($T))) ($s) ($n) ↪ -1
with !seq_find (seq⋅++ ($t) ($ts)) ($s) ($n) ↪ eo⋅⋅ite (!seq_is_prefix (seq⋅++ ($t) ($ts)) ($s)) ($n) (!seq_find ($ts) ($s) (eo⋅⋅add ($n) (1)));
sequential symbol !seq_subsequence [T : Set]: τ (Int ⤳ Int ⤳ (Seq T) ⤳ Seq T);
rule !seq_subsequence ($l) ($u) ({|as|} seq⋅empty (Seq ($T))) ↪ {|as|} seq⋅empty (Seq ($T))
with !seq_subsequence ($l) (0) ($t) ↪ {|as|} seq⋅empty (eo⋅⋅typeof ($t))
with !seq_subsequence (0) ($u) (seq⋅++ (seq⋅unit ($e)) ($ts)) ↪ eo⋅⋅cons seq⋅++ (seq⋅unit ($e)) (!seq_subsequence (0) (eo⋅⋅add ($u) (-1)) ($ts))
with !seq_subsequence ($l) ($u) (seq⋅++ (seq⋅unit ($e)) ($ts)) ↪ !seq_subsequence (eo⋅⋅add ($l) (-1)) (eo⋅⋅add ($u) (-1)) ($ts);
sequential symbol !seq_eval_replace_all_rec [T : Set]: τ ((Seq T) ⤳ (Seq T) ⤳ (Seq T) ⤳ Int ⤳ Int ⤳ Seq T);
rule !seq_eval_replace_all_rec ($s) ($t) ($u) (-1) ($lent) ↪ $s
with !seq_eval_replace_all_rec ($s) ($t) ($u) ($n) ($lent) ↪ (let snext ≔ !seq_subsequence (eo⋅⋅add ($n) ($lent)) (!str_value_len ($s)) ($s) in eo⋅⋅list_concat seq⋅++ (!seq_subsequence (0) ($n) ($s)) (eo⋅⋅list_concat seq⋅++ ($u) (!seq_eval_replace_all_rec snext ($t) ($u) (!seq_find snext ($t) (0)) ($lent))));
sequential symbol !seq_eval [T : Set]: τ (T ⤳ T);
rule !seq_eval (seq⋅nth ($t) ($n)) ↪ (let res ≔ eo⋅⋅list_nth seq⋅++ (!str_to_nary_form ($t) false) ($n) in !seq_element_of_unit res)
with !seq_eval (seq⋅len ($t)) ↪ !str_value_len (!str_nary_intro ($t))
with !seq_eval (seq⋅++ ($t) ($ts)) ↪ !str_nary_elim (eo⋅⋅list_concat seq⋅++ (!str_nary_intro ($t)) (!str_nary_intro (!seq_eval ($ts))))
with !seq_eval (seq⋅extract ($t) ($n) ($m)) ↪ (let tn ≔ !str_nary_intro ($t) in !str_nary_elim (!seq_subsequence ($n) (eo⋅⋅add ($n) ($m)) tn))
with !seq_eval (seq⋅contains ($t) ($s)) ↪ (let tn ≔ !str_nary_intro ($t) in (let sn ≔ !str_nary_intro ($s) in eo⋅⋅not (eo⋅⋅is_neg (!seq_find tn sn (0)))))
with !seq_eval (seq⋅replace ($t) ($s) ($r)) ↪ (let tn ≔ !str_nary_intro ($t) in (let sn ≔ !str_nary_intro ($s) in (let i ≔ !seq_find tn sn (0) in eo⋅⋅ite (eo⋅⋅is_neg i) ($t) (!str_nary_elim (eo⋅⋅list_concat seq⋅++ (!seq_subsequence (0) i tn) (eo⋅⋅list_concat seq⋅++ (!str_nary_intro ($r)) (!seq_subsequence (eo⋅⋅add i (!str_value_len sn)) (!str_value_len tn) tn)))))))
with !seq_eval (seq⋅replace_all ($t) ($s) ($r)) ↪ (let tn ≔ !str_nary_intro ($t) in (let sn ≔ !str_nary_intro ($s) in (let rn ≔ !str_nary_intro ($r) in eo⋅⋅ite (eo⋅⋅eq (!str_value_len ($s)) (0)) ($t) (!str_nary_elim (!seq_eval_replace_all_rec tn sn rn (!seq_find sn tn (0)) (!str_value_len tn))))))
with !seq_eval (seq⋅indexof ($t) ($s) ($n)) ↪ (let tn ≔ !str_nary_intro ($t) in (let sn ≔ !str_nary_intro ($s) in (let tl ≔ !str_value_len tn in !seq_find (!seq_subsequence ($n) tl tn) sn ($n))))
with !seq_eval (seq⋅prefixof ($t) ($s)) ↪ !seq_is_prefix (!str_nary_intro ($t)) (!str_nary_intro ($s))
with !seq_eval (seq⋅suffixof ($t) ($s)) ↪ !seq_is_prefix (!str_to_nary_form ($t) true) (!str_to_nary_form ($s) true)
with !seq_eval (seq⋅at ($t) ($n)) ↪ !seq_eval (seq⋅extract ($t) ($n) (1))
with !seq_eval (seq⋅rev ($t)) ↪ !str_nary_elim (!str_to_nary_form ($t) true)
with !seq_eval ($t) ↪ $t;
