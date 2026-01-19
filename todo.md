# todos.

We get the following error:
  `[.../cpc/theories/Quantifiers.lp:6:5-40] Cannot solve List ≡ $5`
Because of:
```lambdapi
sequential symbol !get_var_list : τ (Bool ⤳ eo.List);
rule !get_var_list ($Q ⋅ $xs ⋅ $G) ↪ $xs;
```
Really, this should be:
```lambdapi
sequential symbol !get_var_list : τ (Bool ⤳ eo.List);
rule !get_var_list ((⋅[eo.List][Bool ⤳ Bool] $Q $xs) ⋅ $G) ↪ $xs;
```
so that lambdapi can check that `$xs` is an `eo.List`.


```lambdapi
symbol t ≔ forall ⋅ (eo.List__cons ⋅ (eo.var "x" Int) ⋅ (eo.List__cons ⋅ (eo.var "y" Int) ⋅ eo.List__nil)) ⋅ true;
```

Probably a similar issue in `AciNorm.lp`:
```lambdapi
sequential symbol !get_ai_norm [T : Set]: τ (T ⤳ T);
rule !get_ai_norm [$T] ($f ⋅ $x ⋅ $y) ↪ let id ≔ eo.nil $f (eo.typeof ($f ⋅ $x ⋅ $y)) in eo.list_singleton_elim $f (!get_ai_norm_rec $f id ($f ⋅ $x ⋅ $y));
```
We need to explicitly give the type of the application
so that lambdapi knows the type of $f for the applications
of `eo.list_singleton_elim` and `!get_ai_norm_rec`??.




Fix bugs.
----------------
<!--- we should overhaul the way we are handling the
  insertion/resolution of implicit parameters in
  declarations/definitions/programs.
    probably we have to to salvage parts of `resolve.ml`
  to do this. for each constant with implicits, we should
  insert and fresh metavariables for each of them,
  generate constraints, perform unification, and solve.-->

- when processing the DAG, - when generating the lambdapi files, we should not even
  generate a file if one its ancestors encounters a bug
  or does not pass through `lambdapi check`.we should run lambdapi check
  each time we finish generating a lambdapi file.
  if a file encounters an issue at any stage, we should stop
  there. we should keep the offending file, so that we can
  view it in our editor afterwards.


Pretty printing.
----------------
- for each lambdapi 'command block' produced by `eo2lp`,
  we should print the corresponding Eunoia "source"
  using the printing functions from `syntax_eo.ml`.

- pretty print & linebreak lambdapi source.
  e.g.,
```lambdapi
sequential symbol !assoc_nil_nth_type [T : Set] [U : Set] [V : Set] [W : Set]: τ ((T ⤳ U ⤳ V) ⤳ W ⤳ Int ⤳ eo.Type);
rule !assoc_nil_nth_type [$T] [$U] [$V] [$W] $f ($f ⋅ $x1 ⋅ $x2) 0 ↪ eo.typeof $x1
with !assoc_nil_nth_type [$T] [$U] [$V] [$W] $f ($f ⋅ $x1 ⋅ $x2) $n ↪ !assoc_nil_nth_type $f $x2 (eo.add $n -1);
```
should be
```lambdapi
sequential symbol !assoc_nil_nth_type
  [T : Set] [U : Set] [V : Set] [W : Set]
  : τ ((T ⤳ U ⤳ V) ⤳ W ⤳ Int ⤳ eo.Type);
rule
  !assoc_nil_nth_type [$T] [$U] [$V] [$W] $f ($f ⋅ $x1 ⋅ $x2) 0
  ↪ eo.typeof $x1
with
  !assoc_nil_nth_type [$T] [$U] [$V] [$W] $f ($f ⋅ $x1 ⋅ $x2) $n
  ↪ !assoc_nil_nth_type $f $x2 (eo.add $n -1);
```
We should only do linebreaking when the result of printing
the line unedited would exceed 60 characters.

- when we encounter eo::quote in an arrow type we should
  turn everything up to the final occurrence into a
  an application of dependent arrow type symbol `⤳d`
  defined thus:
```lambdapi
symbol ⤳d (T : τ Type) : τ (T ⤳ Type) → τ Type;
rule τ ($T ⤳d $F) ↪ (Π x : τ $T, $F x);
```
