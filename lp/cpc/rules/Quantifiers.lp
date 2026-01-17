require open cpc.Core Stdlib.Set cpc.programs.Quantifiers cpc.programs.Datatypes cpc.theories.Quantifiers;
sequential symbol !mk_skolems : τ ({|@List|} ⤳ Bool ⤳ Int ⤳ {|@List|});
rule !mk_skolems ({|@list|} ($x) ($xs)) ($F) ($i) ↪ eo⋅⋅cons {|@list|} ({|@quantifiers_skolemize|} ($F) ($i)) (!mk_skolems ($xs) ($F) (eo⋅⋅add ($i) (1)))
with !mk_skolems {|@list.nil|} ($F) ($i) ↪ {|@list.nil|};
sequential symbol !mk_quant_unused_vars_rec : τ ({|@List|} ⤳ Bool ⤳ eo⋅⋅List);
rule !mk_quant_unused_vars_rec {|@list.nil|} ($F) ↪ {|@list.nil|}
with !mk_quant_unused_vars_rec ({|@list|} ($x) ($xs)) ($F) ↪ (let r ≔ !mk_quant_unused_vars_rec ($xs) ($F) in eo⋅⋅ite (!contains_atomic_term ($F) ($x)) (eo⋅⋅cons {|@list|} ($x) (eo⋅⋅list_erase {|@list|} r ($x))) r);
sequential symbol !mk_quant : τ (({|@List|} ⤳ Bool ⤳ Bool) ⤳ {|@List|} ⤳ Bool ⤳ Bool);
rule !mk_quant ($Q) {|@list.nil|} ($F) ↪ $F
with !mk_quant ($Q) ($x) ($F) ↪ $Q ($x) ($F);
sequential symbol !mk_quant_merge_prenex : τ (({|@List|} ⤳ Bool ⤳ Bool) ⤳ Bool ⤳ {|@List|} ⤳ Bool);
rule !mk_quant_merge_prenex ($Q) ($Q ($x) ($F)) ($y) ↪ !mk_quant_merge_prenex ($Q) ($F) (eo⋅⋅list_concat {|@list|} ($y) ($x))
with !mk_quant_merge_prenex ($Q) ($F) ($y) ↪ $Q ($y) ($F);
sequential symbol !mk_quant_miniscope_and : τ ({|@List|} ⤳ Bool ⤳ Bool);
rule !mk_quant_miniscope_and ($x) (and ($f) ($fs)) ↪ eo⋅⋅cons and (forall ($x) ($f)) (!mk_quant_miniscope_and ($x) ($fs))
with !mk_quant_miniscope_and ($x) true ↪ true;
sequential symbol !is_quant_miniscope_or : τ ({|@List|} ⤳ Bool ⤳ Bool ⤳ Bool);
rule !is_quant_miniscope_or ($x) (or ($f) ($fs)) (or ($f) ($gs)) ↪ eo⋅⋅requires (!contains_atomic_term_list ($f) ($x)) false (!is_quant_miniscope_or ($x) ($fs) ($gs))
with !is_quant_miniscope_or ($x) (or ($f) ($fs)) (or (forall {|@list.nil|} ($f)) ($gs)) ↪ eo⋅⋅requires (!contains_atomic_term_list ($f) ($x)) false (!is_quant_miniscope_or ($x) ($fs) ($gs))
with !is_quant_miniscope_or ({|@list|} ($x) ($xs)) (or ($f) ($fs)) (or (forall ({|@list|} ($x) ($ys)) ($f)) ($gs)) ↪ eo⋅⋅requires (!contains_atomic_term ($gs) ($x)) false (!is_quant_miniscope_or ($xs) (or ($f) ($fs)) (or (forall ($ys) ($f)) ($gs)))
with !is_quant_miniscope_or {|@list.nil|} false false ↪ true
with !is_quant_miniscope_or ($x) ($f) ($g) ↪ false;
symbol !mk_quant_var_elim_eq_subs [T : Set] (x : τ T) (t : τ T) (F : τ Bool)≔ eo⋅⋅requires (!contains_atomic_term t x) false (!substitute x t F);
sequential symbol !mk_quant_var_elim_eq [T : Set]: τ (T ⤳ Bool ⤳ Bool);
rule !mk_quant_var_elim_eq ($x) (not (and (= ($x) ($t)))) ↪ !mk_quant_var_elim_eq_subs ($x) ($t) false
with !mk_quant_var_elim_eq ($x) (or (not (and (= ($x) ($t)))) ($F)) ↪ !mk_quant_var_elim_eq_subs ($x) ($t) (eo⋅⋅list_singleton_elim or ($F));
sequential symbol !is_quant_dt_split_conj [T : Set] [C : Set]: τ (T ⤳ C ⤳ {|@List|} ⤳ Bool ⤳ Bool ⤳ Bool);
rule !is_quant_dt_split_conj ($x) ($c) ({|@list|} ($y) ($ys)) ($F) (forall ({|@list|} ($y) ($zs)) ($G)) ↪ eo⋅⋅requires (!contains_atomic_term ($zs) ($y)) false (!is_quant_dt_split_conj ($x) ($c) ($ys) ($F) (forall ($zs) ($G)))
with !is_quant_dt_split_conj ($x) ($c) {|@list.nil|} ($F) (forall ({|@list|} ($y) ($zs)) ($G)) ↪ eo⋅⋅requires (!contains_atomic_term ($zs) ($y)) false (!is_quant_dt_split_conj ($x) ($c ($y)) {|@list.nil|} ($F) (forall ($zs) ($G)))
with !is_quant_dt_split_conj ($x) ($c) {|@list.nil|} ($F) (forall {|@list.nil|} ($G)) ↪ !is_quant_dt_split_conj ($x) ($c) {|@list.nil|} ($F) ($G)
with !is_quant_dt_split_conj ($x) ($cx) {|@list.nil|} ($F) ($G) ↪ eo⋅⋅eq (!substitute ($x) ($cx) ($F)) ($G);
sequential symbol !is_quant_dt_split [T : Set]: τ (T ⤳ eo⋅⋅List ⤳ {|@List|} ⤳ Bool ⤳ Bool ⤳ Bool);
rule !is_quant_dt_split ($x) (eo⋅⋅List⋅⋅cons ($c) ($cs)) ($ys) ($F) (and ($g) ($G)) ↪ eo⋅⋅requires (!is_quant_dt_split_conj ($x) ($c) ($ys) ($F) ($g)) true (!is_quant_dt_split ($x) ($cs) ($ys) ($F) ($G))
with !is_quant_dt_split ($x) eo⋅⋅List⋅⋅nil ($ys) ($F) true ↪ true
with !is_quant_dt_split ($x) ($cs) ($ys) ($F) ($g) ↪ !is_quant_dt_split ($x) ($cs) ($ys) ($F) (and ($g));
