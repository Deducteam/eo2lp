require open cpc.Core Stdlib.Set cpc.theories.Builtin cpc.theories.Arrays cpc.theories.Arith cpc.theories.BitVectors cpc.theories.Strings cpc.theories.Sets cpc.theories.Datatypes cpc.programs.Utils cpc.programs.Datatypes;
symbol !are_distinct_terms [T : Set] (t : τ T) (s : τ T)≔ eo⋅⋅ite (eo⋅⋅eq t s) false (!are_distinct_terms_list ({|@list|} t s) (eo⋅⋅typeof t));
sequential symbol !some_pairwise_distinct_term : τ ({|@List|} ⤳ {|@List|} ⤳ Bool);
rule !some_pairwise_distinct_term ({|@list|} ($t) ($ts)) ({|@list|} ($s) ($ss)) ↪ eo⋅⋅ite (!are_distinct_terms ($t) ($s)) true (!some_pairwise_distinct_term ($ts) ($ss))
with !some_pairwise_distinct_term {|@list.nil|} {|@list.nil|} ↪ false;
sequential symbol !set_is_not_subset [T : Set]: τ ((Set T) ⤳ (Set T) ⤳ Bool);
rule !set_is_not_subset ({|as|} set⋅empty (Set ($T))) ($s) ↪ false
with !set_is_not_subset (set⋅singleton ($e1)) ({|as|} set⋅empty (Set ($T))) ↪ true
with !set_is_not_subset (set⋅singleton ($e1)) (set⋅singleton ($e2)) ↪ !are_distinct_terms ($e1) ($e2)
with !set_is_not_subset (set⋅singleton ($e1)) (set⋅union (set⋅singleton ($e2)) ($ss)) ↪ eo⋅⋅ite (!are_distinct_terms ($e1) ($e2)) (!set_is_not_subset (set⋅singleton ($e1)) ($ss)) false
with !set_is_not_subset (set⋅union (set⋅singleton ($e1)) ($ts)) ($s) ↪ eo⋅⋅ite (!set_is_not_subset (set⋅singleton ($e1)) ($s)) true (!set_is_not_subset ($ts) ($s));
sequential symbol !seq_distinct_terms [T : Set]: τ ((Seq T) ⤳ (Seq T) ⤳ Bool);
rule !seq_distinct_terms (seq⋅unit ($e1)) ($s) ↪ !seq_distinct_terms (seq⋅++ (seq⋅unit ($e1))) ($s)
with !seq_distinct_terms ($t) (seq⋅unit ($e2)) ↪ !seq_distinct_terms ($t) (seq⋅++ (seq⋅unit ($e2)))
with !seq_distinct_terms (seq⋅++ (seq⋅unit ($e1)) ($ts)) (seq⋅++ (seq⋅unit ($e2)) ($ss)) ↪ eo⋅⋅ite (!are_distinct_terms ($e1) ($e2)) true (!seq_distinct_terms ($ts) ($ss))
with !seq_distinct_terms ($t) ($t) ↪ false
with !seq_distinct_terms ($t) ($s) ↪ true;
sequential symbol !dt_distinct_terms_rec [T : Set] [V : Set]: τ (T ⤳ V ⤳ {|@List|} ⤳ {|@List|} ⤳ Bool);
rule !dt_distinct_terms_rec ($f ($a)) ($cs) ($l1) ($l2) ↪ !dt_distinct_terms_rec ($f) ($cs) (eo⋅⋅cons {|@list|} ($a) ($l1)) ($l2)
with !dt_distinct_terms_rec ($ct) ($f ($a)) ($l1) ($l2) ↪ !dt_distinct_terms_rec ($ct) ($f) ($l1) (eo⋅⋅cons {|@list|} ($a) ($l2))
with !dt_distinct_terms_rec ($ct) ($cs) ($l1) ($l2) ↪ eo⋅⋅ite (eo⋅⋅eq (!dt_is_cons ($ct)) true) (eo⋅⋅ite (eo⋅⋅eq ($ct) ($cs)) (!some_pairwise_distinct_term ($l1) ($l2)) (eo⋅⋅eq (!dt_is_cons ($cs)) true)) false;
symbol !dt_distinct_terms [T : Set] (t : τ T) (s : τ T)≔ !dt_distinct_terms_rec t s {|@list.nil|} {|@list.nil|};
sequential symbol !are_distinct_terms_type [T : Set]: τ (T ⤳ T ⤳ eo⋅⋅Type ⤳ Bool);
rule !are_distinct_terms_type ($t) ($t) ($T) ↪ false
with !are_distinct_terms_type ($t) ($s) Int ↪ eo⋅⋅and (eo⋅⋅is_z ($t)) (eo⋅⋅is_z ($s))
with !are_distinct_terms_type ($t) ($s) Real ↪ eo⋅⋅and (eo⋅⋅is_q ($t)) (eo⋅⋅is_q ($s))
with !are_distinct_terms_type ($t) ($s) String ↪ eo⋅⋅and (eo⋅⋅is_str ($t)) (eo⋅⋅is_str ($s))
with !are_distinct_terms_type ($t) ($s) (BitVec ($n)) ↪ eo⋅⋅and (eo⋅⋅is_bin ($t)) (eo⋅⋅is_bin ($s))
with !are_distinct_terms_type ($t) ($s) Bool ↪ eo⋅⋅and (eo⋅⋅is_bool ($t)) (eo⋅⋅is_bool ($s))
with !are_distinct_terms_type ($st) ($ss) (Set ($U)) ↪ eo⋅⋅or (!set_is_not_subset ($st) ($ss)) (!set_is_not_subset ($ss) ($st))
with !are_distinct_terms_type ($sst) ($sss) (Seq ($U)) ↪ !seq_distinct_terms ($sst) ($sss)
with !are_distinct_terms_type ($t) ($s) ($T) ↪ !dt_distinct_terms ($t) ($s);
sequential symbol !are_distinct_terms_list_rec [T : Set]: τ (T ⤳ {|@List|} ⤳ eo⋅⋅Type ⤳ Bool);
rule !are_distinct_terms_list_rec ($t) ({|@list|} ($s) ($xs)) ($T) ↪ eo⋅⋅ite (!are_distinct_terms_type ($t) ($s) ($T)) (!are_distinct_terms_list_rec ($t) ($xs) ($T)) false
with !are_distinct_terms_list_rec ($t) {|@list.nil|} ($T) ↪ true;
sequential symbol !are_distinct_terms_list : τ ({|@List|} ⤳ eo⋅⋅Type ⤳ Bool);
rule !are_distinct_terms_list {|@list.nil|} ($T) ↪ true
with !are_distinct_terms_list ({|@list|} ($t) ($xs)) ($T) ↪ eo⋅⋅ite (!are_distinct_terms_list_rec ($t) ($xs) ($T)) (!are_distinct_terms_list ($xs) ($T)) false;
