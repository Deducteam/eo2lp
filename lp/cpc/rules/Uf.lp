require open cpc.Core Stdlib.Set cpc.theories.Builtin cpc.programs.Nary cpc.programs.DistinctValues;
sequential symbol !mk_symm : τ (Bool ⤳ Bool);
rule !mk_symm (and (= ($t1) ($t2))) ↪ and (= ($t2) ($t1))
with !mk_symm (not (and (= ($t1) ($t2)))) ↪ not (and (= ($t2) ($t1)));
sequential symbol !mk_trans [U : Set]: τ (U ⤳ U ⤳ Bool ⤳ Bool);
rule !mk_trans ($t1) ($t2) (and (and (= ($t3) ($t4))) ($tail)) ↪ eo⋅⋅requires ($t2) ($t3) (!mk_trans ($t1) ($t4) ($tail))
with !mk_trans ($t1) ($t2) true ↪ and (= ($t1) ($t2));
sequential symbol !mk_cong_rhs [U : Set]: τ (U ⤳ Bool ⤳ U);
rule !mk_cong_rhs ($f ($t1)) (and (and (= ($t1) ($t2))) ($tail)) ↪ !mk_cong_rhs ($f) ($tail) ($t2)
with !mk_cong_rhs ($f) true ↪ $f;
sequential symbol !mk_nary_cong_rhs [U : Set]: τ (U ⤳ Bool ⤳ U);
rule !mk_nary_cong_rhs ($f ($s1) ($t)) (and (and (= ($s1) ($s2))) ($tail)) ↪ eo⋅⋅cons ($f) ($s2) (!mk_nary_cong_rhs ($t) ($tail))
with !mk_nary_cong_rhs ($nil) true ↪ $nil;
sequential symbol !mk_ho_cong [U : Set]: τ (U ⤳ U ⤳ Bool ⤳ Bool);
rule !mk_ho_cong ($f1) ($f2) (and (and (= ($t1) ($t2))) ($tail)) ↪ !mk_ho_cong ($f1 ($t1)) ($f2 ($t2)) ($tail)
with !mk_ho_cong ($t1) ($t2) true ↪ and (= ($t1) ($t2));
sequential symbol !mk_distinct_elim_rec [T : Set]: τ (T ⤳ {|@List|} ⤳ Bool ⤳ Bool);
rule !mk_distinct_elim_rec ($x) ({|@list|} ($y) ($xs)) ($b) ↪ eo⋅⋅cons and (not (and (= ($x) ($y)))) (!mk_distinct_elim_rec ($x) ($xs) ($b))
with !mk_distinct_elim_rec ($x) {|@list.nil|} ($b) ↪ $b;
sequential symbol !mk_distinct_elim : τ (Bool ⤳ Bool);
rule !mk_distinct_elim (distinct ($x) ($xs)) ↪ !mk_distinct_elim_rec ($x) ($xs) (!mk_distinct_elim (distinct ($xs)))
with !mk_distinct_elim (distinct ($xs)) ↪ true;
