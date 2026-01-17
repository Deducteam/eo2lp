require open cpc.Core Stdlib.Set cpc.theories.Arith;
sequential symbol !assoc_nil_nth_type [T : Set] [U : Set] [V : Set] [W : Set]: τ ((T ⤳ U ⤳ V) ⤳ W ⤳ Int ⤳ eo⋅⋅Type);
rule !assoc_nil_nth_type ($f) ($f ($x1) ($x2)) (0) ↪ eo⋅⋅typeof ($x1)
with !assoc_nil_nth_type ($f) ($f ($x1) ($x2)) ($n) ↪ !assoc_nil_nth_type ($f) ($x2) (eo⋅⋅add ($n) (-1));
sequential symbol !assoc_nil_nth [f : τ (T ⤳ U ⤳ V)] [n : τ Int] [x : τ W]: τ ((eo⋅⋅quote f) ⤳ (eo⋅⋅quote x) ⤳ (eo⋅⋅quote n) ⤳ !assoc_nil_nth_type f x n);
rule !assoc_nil_nth ($f) ($f ($x1) ($x2)) (0) ↪ $x1
with !assoc_nil_nth ($f) ($f ($x1) ($x2)) ($n) ↪ !assoc_nil_nth ($f) ($x2) (eo⋅⋅add ($n) (-1));
