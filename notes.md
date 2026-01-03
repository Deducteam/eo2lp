-----------------
# 2026-01-02
-----------------
Overloading. Ugh.
`theories.Arith` declares the symbol `-` as a constant twice.
First, binary subtraction.
`constant symbol - [T : Set] [U : Set] : τ (T ⤳ U ⤳ (!arith_typeunion T U));`
Then, unary negation.
`constant symbol - [T : Set] : τ (T ⤳ (eo.requires_type_out (!is_arith_type T) true T));`

We need to handle this somehow.
Naive: during elaboration, if we encounter a duplicate symbol,
we add some suffix. (e.g., `-` --> `-_1`)

Final symbol chosen based on types of `k` and args.
We choose the first symbol such that
  `k t1 .. tn` is well-typed.
But this is hard, because at resolution-time, we are only
dealing with binary applications.... and at elaboration
time, we don't have the machinery to check the types of
everything.

So perhaps, use list-wise application in elaborated
terms and change our resolution algorithm... and allow
symbols to have multiple types in signature.



-----------------
# 2025-12-27
-----------------
Example of a program where we NEED to insert explicits
on the left hand side:
```lambdapi
sequential symbol {|$evaluate_internal|} [T : Set] : El (T ⤳ {|eo::List|} ⤳ T);
rule {|$evaluate_internal|} [$T] $t ({|eo::List::cons|} [$T] ▫ $tev ▫ {|eo::List::nil|}) ↪ $tev;
```
Suppose lambdapi generates two metavariables `?lhs`, `?rhs`
for the types of the left-hand and right-hand sides of
the rewrite rule.

The first insertion `{|$evaluate_internal|} [$T]` tells us
that `?lhs == $T`, and the second `{|eo::List::cons|} [$T]`
tells us that `$tev : $T`, hence `?rhs == $T`.
Thus `?lhs == ?rhs`.


Example of a program where insertion on the rhs causes issues:
```lambdapi
sequential symbol {|$is_app|} [T : Set] [U : Set] [V : Set] : El ((T ⤳ U) ⤳ V ⤳ Bool);
rule {|$is_app|} [$T] [$U] [$U] $f ($f ▫ $x) ↪ true
with {|$is_app|} [$T] [$U] [$V] $f ($g ▫ $x) ↪ {|$is_app|} [$T] [$U] [$T ⤳ $V] $f $g;
```
I think the issue here is with `g`.
The insertion of `[$V]` on the lhs forces `($g ▫ $x) : El $V`,
which leaves `$g` to have some type `El (?n ⤳ $V)`.
Then, on the rhs, we try to force `$g : El ($T ⤳ $V)`,
but lambdapi can't prove that `?n == $V`, so we fail.

However, if don't insert any explicits on the rhs,
we never generate any constraints for `?n`, and we are fine.


An easier example of a program with faulty rhs inserts:
```lambdapi
sequential symbol {|$get_arg_list_rec|} [S : Set] : El (S ⤳ {|eo::List|} ⤳ {|eo::List|});
rule {|$get_arg_list_rec|} [$S] ($f ▫ $x) $acc ↪ {|$get_arg_list_rec|} [$T ⤳ $S] $f ({|eo::cons|} [$T] [{|eo::List|}] ({|eo::List::cons|} [$T]) $x $acc)
with {|$get_arg_list_rec|} [$S] $y $acc ↪ $acc;
```
The pattern variable `$T` doesn't appear on the lhs,
so we can't insert it.

All of these problems arise from the fact that Eunoia's
programs have a context that give the types for all
"pattern variables" appearing in the rules.
  In LambdaPi, we don't, but we still need to prove type
preservation. So we perform resolution on the terms to
insert explicits, which forces the types of most pattern
variables.

The current solution for this is to not insert explicits
on the right-hand side of rules during translation.


-----------------
# 2025-12-19
-----------------
We need to implement a mechanism for binding free schematic
variables in post-elaboration commands. e.g.;
```
Elaborating: (define @pair () @@pair)

  Begin resolving `@@pair⟨U ↦ ?U0, T ↦ ?T0⟩`
  Resolved:
    `@@pair⟨U ↦ ?U0, T ↦ ?T0⟩`
  with type
    `(~> ?U0 ?T0 ((@Pair⟨⟩ ⋅ ?U0) ⋅ ?T0))`

Done:
  define @pair⟨⟩
    : (~> ?U0 ?T0 ((@Pair⟨⟩ ⋅ ?U0) ⋅ ?T0))
    := @@pair⟨U ↦ ?U0, T ↦ ?T0⟩
```

We need to update the signature so that @pair has two
parameters {U, T} and then update the body of the
definition with this assignment.

Some procedure called 'bind_svars'.
For each free schematic var, we choose a name.

  SVar (s,0) -> Var s
  SVar (s,i) -> Var (s ^ string_of_int i)

We use this list of variables as our (implicit) parameters for @@pair.
Then we replace the schematic vars in the body with our choice
using `svmap_subst`.


# 2025-12-20

(* (unresolved) metavars can only come from constants.
  so really, a 'parameter map' should hold the parameters,
  along with some information about its instantiation.
  kind of like an option type.

  so to collect all free mvars, we need to look at all
  constants and their parameter maps. if it maps to a
  metavariable, we consider it 'free'

*)

can we simplify mvmaps and param maps??
it feels like we shouldn't need both.

consider changing Const constructor to just take a string
and a list of terms for the parameter instantiations.
when we initialize, we lookup the params of the constant
in the signature, then generate metavars for them.

for binding lingering mvars, we need to be able to know
the type of the metavar. otherwise, there's no need to
remember the 'original initialization site' of the metavar.

it just matters that they have unique names.
do this after lunch and chores.


also, it's quite important that we consider how params
are handled during desugaring and resolution.

# 2025-12-21

It feels possible that elaboration should process the
local context (param list), followed by the body.
  Perhaps there are constraints generated in the local
context that cannot be resolved alone (without the
constraints generated when inferring the body).
  But I'm skeptical of this. I think we just need to
elaborate the parameters sequentially.
