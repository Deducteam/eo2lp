require cpc.Prelude as eo;
require open cpc.theories.Builtin cpc.theories.Ints cpc.programs.Nary;

sequential symbol {|$to_clause|} : τ (Bool ⤳ Bool);
sequential symbol {|$from_clause|} : τ (Bool ⤳ Bool);
symbol {|$remove_maybe_self|} (l : τ Bool) (C : τ Bool) ≔ @{|eo::ite|} Bool Bool (@{|eo::eq|} Bool Bool l C) false (@{|eo::list_erase|} Bool Bool or C l);
symbol {|$resolve|} (C1 : τ Bool) (C2 : τ Bool) (pol : τ Bool) (L : τ Bool) ≔ @APP _ _ {|$from_clause|} (@{|eo::list_concat|} _ _ or ({|$remove_maybe_self|} (@{|eo::ite|} _ _ pol L (@APP _ _ not L)) (@APP _ _ {|$to_clause|} C1)) ({|$remove_maybe_self|} (@{|eo::ite|} _ _ pol (@APP _ _ not L) L) (@APP _ _ {|$to_clause|} C2)));
sequential symbol {|$chain_m_resolve_rec_step|} : τ ({|@@Pair|} Bool Bool ⤳ (Bool ⤳ (Bool ⤳ (Bool ⤳ {|@@Pair|} Bool Bool))));
sequential symbol {|$chain_m_resolve_rec|} : τ (Bool ⤳ ({|eo::List|} ⤳ ({|eo::List|} ⤳ {|@@Pair|} Bool Bool)));
sequential symbol {|$chain_m_resolve_final|} : τ (Bool ⤳ ({|@@Pair|} Bool Bool ⤳ Bool));
sequential symbol {|$chain_m_resolve|} : τ (Bool ⤳ ({|eo::List|} ⤳ ({|eo::List|} ⤳ Bool)));
sequential symbol {|$lower_not_and|} : τ (Bool ⤳ Bool);
