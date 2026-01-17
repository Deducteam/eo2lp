require open cpc.Core Stdlib.Set cpc.theories.Sets cpc.programs.DistinctValues;
sequential symbol !set_union_to_list [T : Set]: τ ((Set T) ⤳ {|@List|});
rule !set_union_to_list (set⋅union (set⋅singleton ($e)) ($t)) ↪ eo⋅⋅cons {|@list|} ($e) (!set_union_to_list ($t))
with !set_union_to_list ({|as|} set⋅empty (Set ($T))) ↪ {|@list.nil|}
with !set_union_to_list (set⋅singleton ($e)) ↪ {|@list|} ($e);
sequential symbol !eval_sets_inter : τ ({|@List|} ⤳ {|@List|} ⤳ {|@List|});
rule !eval_sets_inter ({|@list|} ($a) {|as|}) ($bs) ↪ (let r ≔ !eval_sets_inter {|as|} ($bs) in eo⋅⋅ite (eo⋅⋅is_neg (eo⋅⋅list_find {|@list|} ($bs) ($a))) (eo⋅⋅requires (!are_distinct_terms_list_rec ($a) ($bs) (eo⋅⋅typeof ($a))) true r) (eo⋅⋅cons {|@list|} ($a) r))
with !eval_sets_inter {|@list.nil|} ($bs) ↪ {|@list.nil|};
sequential symbol !eval_sets_minus : τ ({|@List|} ⤳ {|@List|} ⤳ {|@List|});
rule !eval_sets_minus ({|@list|} ($a) {|as|}) ($bs) ↪ (let r ≔ !eval_sets_minus {|as|} ($bs) in eo⋅⋅ite (eo⋅⋅is_neg (eo⋅⋅list_find {|@list|} ($bs) ($a))) (eo⋅⋅requires (!are_distinct_terms_list_rec ($a) ($bs) (eo⋅⋅typeof ($a))) true (eo⋅⋅cons {|@list|} ($a) r)) r)
with !eval_sets_minus {|@list.nil|} ($bs) ↪ {|@list.nil|};
sequential symbol !eval_sets_op [T : Set]: τ ((Set T) ⤳ {|@List|});
rule !eval_sets_op (set⋅union ($s) ($t)) ↪ eo⋅⋅list_concat {|@list|} (!set_union_to_list ($s)) (!set_union_to_list ($t))
with !eval_sets_op (set⋅inter ($s) ($t)) ↪ !eval_sets_inter (!set_union_to_list ($s)) (!set_union_to_list ($t))
with !eval_sets_op (set⋅minus ($s) ($t)) ↪ !eval_sets_minus (!set_union_to_list ($s)) (!set_union_to_list ($t));
sequential symbol !set_eval_insert [T : Set]: τ ({|@List|} ⤳ (Set T) ⤳ Set T);
rule !set_eval_insert ({|@list|} ($x) ($xs)) ($t) ↪ set⋅union (set⋅singleton ($x)) (!set_eval_insert ($xs) ($t))
with !set_eval_insert {|@list.nil|} ($t) ↪ $t;
