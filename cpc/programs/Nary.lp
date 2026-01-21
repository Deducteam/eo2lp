require cpc.Prelude as eo;
require open cpc.theories.Arith;
sequential symbol !assoc_nil_nth_type [T : Set] [U : Set] [V : Set] [W : Set]: τ ((T ⤳ U ⤳ V) ⤳ W ⤳ Int ⤳ eo.Type);
rule !assoc_nil_nth_type [$T] [$U] [$V] [$W] $f ($f ⋅ $x1 ⋅ $x2) 0 ↪ $T
with !assoc_nil_nth_type [$T] [$U] [$V] [$W] $f ($f ⋅ $x1 ⋅ $x2) $n ↪ !assoc_nil_nth_type $f $x2 (eo.add $n -1);
sequential symbol !assoc_nil_nth [T : Set] [U : Set] [V : Set] [W : Set]: τ ((T ⤳ U ⤳ V) ⤳d (λ (f : τ (T ⤳ U ⤳ V)), W ⤳d (λ (x : τ W), Int ⤳d (λ (n : τ Int), !assoc_nil_nth_type f x n))));
rule !assoc_nil_nth [$T] [$U] [$V] [$W] $f ($f ⋅ $x1 ⋅ $x2) 0 ↪ $x1
with !assoc_nil_nth [$T] [$U] [$V] [$W] $f ($f ⋅ $x1 ⋅ $x2) $n ↪ !assoc_nil_nth $f $x2 (eo.add $n -1);
