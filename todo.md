# todos.
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
  depedent arrow type symbol `⤳d`.

- handle insertion/resolution of implicit parameters
  in declarations/definitions/programs. the best way to
  do this is to probably to salvage/mutate `resolve.ml`
  and algorithm for inserting metavariables for implicit
  args and then resolving them.
    Perhaps this should be done by `api_lp.ml`, but maybe not.

- handle eo.quote by making a dependent type.
