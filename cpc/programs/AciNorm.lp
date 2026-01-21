require cpc.Prelude as eo;
require open cpc.programs.Utils;
sequential symbol !get_ai_norm_rec [T : Set]: τ ((T ⤳ T ⤳ T) ⤳ T ⤳ T ⤳ T);
rule !get_ai_norm_rec [$T] $f $id ($f ⋅ $x1 ⋅ $x2) ↪ eo.list_setof $f (eo.list_concat $f (!get_ai_norm_rec $f $id $x1) (!get_ai_norm_rec $f $id $x2))
with !get_ai_norm_rec [$T] $f $id $id ↪ $id
with !get_ai_norm_rec [$T] $f $id $x ↪ eo.cons $f $x $id;
sequential symbol !get_ai_norm [T : Set]: τ (T ⤳ T);
rule !get_ai_norm [$T] ($f ⋅ $x ⋅ $y) ↪ let id ≔ eo.nil $f (eo.typeof ($f ⋅ $x ⋅ $y)) in eo.list_singleton_elim $f (!get_ai_norm_rec $f id ($f ⋅ $x ⋅ $y));
sequential symbol !get_a_norm_rec [T : Set]: τ ((T ⤳ T ⤳ T) ⤳ T ⤳ T ⤳ T);
rule !get_a_norm_rec [$T] $f $id ($f ⋅ $x1 ⋅ $x2) ↪ eo.list_concat $f (!get_a_norm_rec $f $id $x1) (!get_a_norm_rec $f $id $x2)
with !get_a_norm_rec [$T] $f $id $id ↪ $id
with !get_a_norm_rec [$T] $f $id $x ↪ eo.cons $f $x $id;
sequential symbol !get_a_norm [U : Set]: τ (U ⤳ U);
rule !get_a_norm [$U] ($f ⋅ $x ⋅ $y) ↪ let id ≔ eo.nil $f (eo.typeof ($f ⋅ $x ⋅ $y)) in eo.list_singleton_elim $f (!get_a_norm_rec $f id ($f ⋅ $x ⋅ $y));
constant symbol aci_sorted [U : Set] [T : Set]: τ (U ⤳ T ⤳ T);
sequential symbol !aci_norm_eq [U : Set]: τ (U ⤳ U ⤳ Bool);
rule !aci_norm_eq [$U] $t $t ↪ true
with !aci_norm_eq [$U] (aci_sorted ⋅ $f ⋅ $t) $t ↪ true
with !aci_norm_eq [$U] (aci_sorted ⋅ $f ⋅ $t) (aci_sorted ⋅ $f ⋅ $s) ↪ eo.list_meq $f $t $s
with !aci_norm_eq [$U] $t $s ↪ false;
symbol !is_aci_norm [S : Set] (a : τ S) (b : τ S) (an : τ S) (bn : τ S) ≔ eo.ite (!aci_norm_eq an b) true (eo.ite (!aci_norm_eq bn a) true (!aci_norm_eq an bn));
