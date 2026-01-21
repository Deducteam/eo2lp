require cpc.Prelude as eo;
require open cpc.theories.Datatypes;
sequential symbol !dt_get_constructors [U : Set]: τ (U ⤳ eo.List);
rule !dt_get_constructors [$U] (Tuple ⋅ $T1 ⋅ $T2) ↪ eo.cons eo.List__cons tuple ∎
with !dt_get_constructors [$U] UnitTuple ↪ eo.cons eo.List__cons tuple_unit ∎
with !dt_get_constructors [$U] ($DC ⋅ $T) ↪ !dt_get_constructors $DC
with !dt_get_constructors [$U] $D ↪ eo.dt_constructors $D;
symbol !dt_inst_cons_of (D : Set) [T : Set] (c : τ T) ≔ !assoc_nil_nth eo.List__cons (eo.dt_constructors D) (eo.list_find eo.List__cons (!dt_get_constructors D) c);
sequential symbol !tuple_get_selectors_rec : τ (eo.Type ⤳ Int ⤳ eo.List);
rule !tuple_get_selectors_rec UnitTuple $n ↪ ∎
with !tuple_get_selectors_rec (Tuple ⋅ $T1 ⋅ $T2) $n ↪ eo.cons eo.List__cons (tuple_select ⋅ $n) (!tuple_get_selectors_rec $T2 (eo.add $n 1));
sequential symbol !dt_get_selectors [T : Set]: τ (eo.Type ⤳ T ⤳ eo.List);
rule !dt_get_selectors [$T] (Tuple ⋅ $T1 ⋅ $T2) tuple ↪ !tuple_get_selectors_rec (Tuple $T1 $T2) 0
with !dt_get_selectors [$T] UnitTuple tuple_unit ↪ ∎
with !dt_get_selectors [$T] $D $c ↪ eo.dt_selectors $c;
sequential symbol !dt_get_selectors_of_app [T : Set]: τ (eo.Type ⤳ T ⤳ eo.List);
rule !dt_get_selectors_of_app [$T] $T ($f ⋅ $a) ↪ !dt_get_selectors_of_app $T $f
with !dt_get_selectors_of_app [$T] $T $a ↪ !dt_get_selectors $T $a;
symbol !dt_is_cons [T : Set] (t : τ T) ≔ eo.ite (eo.is_eq t tuple) true (eo.is_ok (eo.dt_selectors t));
sequential symbol !dt_arg_list [T : Set]: τ (T ⤳ eo.List);
rule !dt_arg_list [$T] (tuple ⋅ $t1 ⋅ $t2) ↪ eo.cons eo.List__cons $t1 (!dt_arg_list $t2)
with !dt_arg_list [$T] $t ↪ !get_arg_list $t;
symbol !dt_arg_nth [T : Set] (t : τ T) (n : τ Int) ≔ !assoc_nil_nth eo.List__cons (!dt_arg_list t) n;
sequential symbol !dt_eq_cons [T : Set] [V : Set]: τ (T ⤳ V ⤳ Bool);
rule !dt_eq_cons [$T] [$V] ($f ⋅ $a) $cs ↪ !dt_eq_cons $f $cs
with !dt_eq_cons [$T] [$V] $ct ($f ⋅ $a) ↪ !dt_eq_cons $ct $f
with !dt_eq_cons [$T] [$V] $ct $cs ↪ eo.requires (!dt_is_cons $ct) true (eo.ite (eo.eq $ct $cs) true (eo.requires (!dt_is_cons $cs) true false));
sequential symbol !tuple_nth [T : Set]: τ (T ⤳ Int ⤳d (λ (n : τ Int), eo.list_nth Tuple T n));
rule !tuple_nth [$T] (tuple ⋅ $s ⋅ $ts) 0 ↪ $s
with !tuple_nth [$T] (tuple ⋅ $s ⋅ $ts) $n ↪ !tuple_nth $ts (eo.add $n -1);
