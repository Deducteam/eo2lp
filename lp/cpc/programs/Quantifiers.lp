require open cpc.Core Stdlib.Set cpc.theories.Builtin cpc.theories.Quantifiers;
sequential symbol !contains_atomic_term [U : Set] [S : Set]: τ (S ⤳ U ⤳ Bool);
rule !contains_atomic_term ($f ($a)) ($x) ↪ eo⋅⋅ite (!contains_atomic_term ($f) ($x)) true (!contains_atomic_term ($a) ($x))
with !contains_atomic_term ($x) ($y) ↪ eo⋅⋅eq ($x) ($y);
sequential symbol !contains_atomic_term_list [T : Set]: τ (T ⤳ {|@List|} ⤳ Bool);
rule !contains_atomic_term_list ($f ($a)) ($xs) ↪ eo⋅⋅ite (!contains_atomic_term_list ($f) ($xs)) true (!contains_atomic_term_list ($a) ($xs))
with !contains_atomic_term_list ($x) ($xs) ↪ eo⋅⋅not (eo⋅⋅is_neg (eo⋅⋅list_find {|@list|} ($xs) ($x)));
sequential symbol !contains_atomic_term_list_free_rec [T : Set]: τ (T ⤳ {|@List|} ⤳ {|@List|} ⤳ Bool);
rule !contains_atomic_term_list_free_rec ($q ({|@list|} ($x) ($ys)) ($a)) ($xs) ($bvs) ↪ !contains_atomic_term_list_free_rec ($a) ($xs) (eo⋅⋅list_concat {|@list|} ({|@list|} ($x) ($ys)) ($bvs))
with !contains_atomic_term_list_free_rec ($f ($a)) ($xs) ($bvs) ↪ eo⋅⋅ite (!contains_atomic_term_list_free_rec ($f) ($xs) ($bvs)) true (!contains_atomic_term_list_free_rec ($a) ($xs) ($bvs))
with !contains_atomic_term_list_free_rec ($x) ($xs) ($bvs) ↪ eo⋅⋅ite (eo⋅⋅is_neg (eo⋅⋅list_find {|@list|} ($xs) ($x))) false (eo⋅⋅is_neg (eo⋅⋅list_find {|@list|} ($bvs) ($x)));
symbol !contains_atomic_term_list_free [T : Set] (x : τ T) (xs : τ {|@List|})≔ !contains_atomic_term_list_free_rec x xs {|@list.nil|};
sequential symbol !substitute [U : Set] [S : Set]: τ (S ⤳ S ⤳ U ⤳ U);
rule !substitute ($x) ($y) ($q ({|@list|} ($v) ($vs)) ($a)) ↪ eo⋅⋅requires (!contains_atomic_term_list_free ($y) ({|@list|} ($v) ($vs))) false ($q (!substitute ($x) ($y) ({|@list|} ($v) ($vs))) (!substitute ($x) ($y) ($a)))
with !substitute ($x) ($y) ($f ($a)) ↪ !substitute ($x) ($y) ($f) (!substitute ($x) ($y) ($a))
with !substitute ($x) ($y) ($x) ↪ $y
with !substitute ($x) ($y) ($z) ↪ $z;
sequential symbol !substitute_simul [S : Set]: τ (S ⤳ {|@List|} ⤳ {|@List|} ⤳ S);
rule !substitute_simul ($q ({|@list|} ($v) ($vs)) ($a)) ($xs) ($ss) ↪ eo⋅⋅requires (!contains_atomic_term_list_free ($ss) ({|@list|} ($v) ($vs))) false ($q (!substitute_simul ({|@list|} ($v) ($vs)) ($xs) ($ss)) (!substitute_simul ($a) ($xs) ($ss)))
with !substitute_simul ($f ($a)) ($xs) ($ss) ↪ !substitute_simul ($f) ($xs) ($ss) (!substitute_simul ($a) ($xs) ($ss))
with !substitute_simul ($x) ($xs) ($ss) ↪ (let i ≔ eo⋅⋅list_find {|@list|} ($xs) ($x) in eo⋅⋅ite (eo⋅⋅is_neg i) ($x) (!assoc_nil_nth {|@list|} ($ss) i));
sequential symbol !beta_reduce_type : τ (eo⋅⋅Type ⤳ {|@List|} ⤳ eo⋅⋅Type);
rule !beta_reduce_type (($T) ⤳ $U) ({|@list|} ($x) ($xs)) ↪ !beta_reduce_type ($U) ($xs)
with !beta_reduce_type ($T) {|@list.nil|} ↪ $T;
sequential symbol !beta_reduce [u : τ U] [ss : τ {|@List|}]: τ ((eo⋅⋅quote u) ⤳ (eo⋅⋅quote ss) ⤳ !beta_reduce_type (eo⋅⋅typeof u) ss);
rule !beta_reduce (lambda ({|@list|} ($x) ($xs)) ($t) ($a)) {|@list.nil|} ↪ (let st ≔ !substitute ($x) ($a) ($t) in eo⋅⋅ite (eo⋅⋅eq ($xs) {|@list.nil|}) st (lambda ($xs) st))
with !beta_reduce (lambda ($xs) ($t)) ($ss) ↪ !substitute_simul ($t) ($xs) ($ss)
with !beta_reduce ($f ($a)) ($ss) ↪ !beta_reduce ($f) ({|@list|} ($a) ($ss));
