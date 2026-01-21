require cpc.Prelude as eo;
require open cpc.theories.Builtin cpc.theories.Ints cpc.programs.Nary;
sequential symbol !to_clause : τ (Bool ⤳ Bool);
rule !to_clause (or ⋅ $F1 ⋅ $F2) ↪ or ⋅ $F1 ⋅ $F2
with !to_clause false ↪ false
with !to_clause $F1 ↪ or ⋅ $F1 ⋅ false;
sequential symbol !from_clause : τ (Bool ⤳ Bool);
rule !from_clause (or ⋅ $F1 ⋅ $F2) ↪ eo.ite (eo.eq $F2 false) $F1 (or ⋅ $F1 ⋅ $F2)
with !from_clause $F1 ↪ $F1;
symbol !remove_maybe_self (l : τ Bool) (C : τ Bool) ≔ eo.ite (eo.eq l C) false (eo.list_erase or C l);
symbol !resolve (C1 : τ Bool) (C2 : τ Bool) (pol : τ Bool) (L : τ Bool) ≔ let lp ≔ eo.ite pol L (not ⋅ L) in let ln ≔ eo.ite pol (not ⋅ L) L in !from_clause (eo.list_concat or (!remove_maybe_self lp (!to_clause C1)) (!remove_maybe_self ln (!to_clause C2)));
sequential symbol !chain_m_resolve_rec_step : τ ((Pair Bool Bool) ⤳ Bool ⤳ Bool ⤳ Bool ⤳ Pair Bool Bool);
rule !chain_m_resolve_rec_step (pair ⋅ $Cr ⋅ $rl) $Cc $pol $L ↪ let lp ≔ eo.ite $pol $L (not ⋅ $L) in let ln ≔ eo.ite $pol (not ⋅ $L) $L in let rln ≔ or ⋅ ln ⋅ $rl in let rlp ≔ or ⋅ lp ⋅ $rl in eo.ite (eo.eq ln $Cc) (pair ⋅ $Cr ⋅ rlp) (pair ⋅ (eo.list_concat or (eo.list_diff or $Cc rln) $Cr) ⋅ rlp);
sequential symbol !chain_m_resolve_rec : τ (Bool ⤳ eo.List ⤳ eo.List ⤳ Pair Bool Bool);
rule !chain_m_resolve_rec true ∎ ∎ ↪ pair ⋅ false ⋅ false
with !chain_m_resolve_rec (and ⋅ $C1 ⋅ $Cs) (eo.List__cons [Bool] ⋅ $pol ⋅ $pols) (eo.List__cons [Bool] ⋅ $L ⋅ $lits) ↪ !chain_m_resolve_rec_step (!chain_m_resolve_rec $Cs $pols $lits) $C1 $pol $L;
sequential symbol !chain_m_resolve_final : τ (Bool ⤳ (Pair Bool Bool) ⤳ Bool);
rule !chain_m_resolve_final $C1 (pair ⋅ $C2 ⋅ (or ⋅ $L ⋅ $rl)) ↪ eo.ite (eo.eq $C1 $L) $C2 (eo.list_concat or (eo.list_diff or $C1 (or ⋅ $L ⋅ $rl)) $C2);
sequential symbol !chain_m_resolve : τ (Bool ⤳ eo.List ⤳ eo.List ⤳ Bool);
rule !chain_m_resolve (and ⋅ $C1 ⋅ $C2) $pols $lits ↪ !chain_m_resolve_final $C1 (!chain_m_resolve_rec $C2 $pols $lits);
sequential symbol !lower_not_and : τ (Bool ⤳ Bool);
rule !lower_not_and true ↪ false
with !lower_not_and (and ⋅ $l ⋅ $ls) ↪ eo.cons or (not ⋅ $l) (!lower_not_and $ls);
