----------
2026-01-24
----------
Thinking about automatic encoding of Eunoia in LambdaPi.

When encoding terms, we need `enc_sym` to detect how
many implicit args a symbol has in its type and apply
as many wildcards as needed. We will use `lambdapi`'s
internal mechanisms to infer the correct values of these
wildcards.

We should almost always use the flag `print_implicits` so
that any lambdapi source we generate will always print
symbols with the `@` prefix, forcing printing of either
wildcards or solutions to those wildcards that we obtain
via resolution.

Consider some of the challenges of encoding `Utils.lp`:

## $compare_geq
Consider the following definition from `programs/Utils.eo`:
```eo
(define $compare_geq ((T Type :implicit) (x T) (y T))
  (eo::ite (eo::eq x y) true (eo::gt x y)))
```
Easy one. This should encode as:
```lp
symbol {|$compare_geq|} ≔
  λ [T : Set] (x : τ T) (y : τ T),
    @{|eo::ite|} _ _ (@{|eo::eq|} _ _ x y) true (@{|eo::gt|} _ _ x y)
```
and resolve to:
```lp
symbol {|$compare_geq|} ≔
  λ [T : Set] (x : τ T) (y : τ T),
    @{|eo::ite|} Bool Bool (@{|eo::eq|} T T x y) true (@{|eo::gt|} T T x y)
```

## Pair type constructors
Consider the :
```eo
(declare-const @@Pair (-> Type Type Type))
(define @Pair () @@Pair)
(declare-parameterized-const @@pair
  ((U Type :implicit) (T Type :implicit))
  (-> U T (@Pair U T)))
(define @pair () @@pair)
```
Whose encodings produce the following source:
```lp
constant symbol {|@@Pair|} : Set → Set → Set;
symbol {|@Pair|} ≔ {|@@Pair|};
constant symbol {|@@pair|} : Π [U T],  τ (U ⤳ T ⤳ ({|@@Pair|} U T));
symbol {|@pair|} ≔ @{|@@pair|} _ _;
```
The definition of `@pair` fails because of unsolved mvars.
Really, we should have:
```lp
symbol {|@pair|} ≔ λ [v1 v2], (@{|@@pair|} v1 v2);
```
where `v1` and `v2` are fresh names.

## eo::List and @list
Now, consider the following declarations in `Prelude.lp`.
```lp
constant symbol {|eo::List|} : Set;
constant symbol {|eo::List::nil|} : τ {|eo::List|};
constant symbol {|eo::List::cons|} : Π [T], El (T ⤳ {|eo::List|} ⤳ {|eo::List|});
```
Then in `Utils.eo` we have:
```eo
(define @List () eo::List)
(define @list.nil () eo::List::nil)
(define @list () eo::List::cons)
```
So we do:
```lp
symbol {|@List|} ≔ {|eo::List|};
symbol {|@list.nil|} ≔ {|eo::List::nil|};
symbol {|@list|} ≔ @{|eo::List::cons|} _;
```
Defining `@list` has the same problem as `@pair`.
The fix is the same.
```lp
symbol {|@list|} ≔ λ [v1], @{|eo::List::cons|} v1;
```

Also, `eo::List::cons` has the `:right-assoc-nil` attribute
with terminator `eo::List::nil`, but I am not sure whether
applications of `@list` inherit the attribute from the
underlying symbol.

Can you please run some tests with `ethos` and check?

The easiest way to handle this may just be expanding
'macro'-like definitions like `@list` and `@pair` during
elaboration-time. That way, any nary applications will
be handled correctly and we don't need to insert implicits
for the unsolved metavars.

## Encoding a program using Eunoia parameter information.

This example involves encoding the following Eunoia program:
```eo
(program $evaluate_internal ((T Type) (t T) (tev T))
  :signature (T @List) T
  (
    (($evaluate_internal t (@list tev)) tev)
  )
)
```
First, note that the `:signature` attribute provides a type
that (naively) encodes to `El (T ⤳ {|eo::List|} ⤳ T)`.
But we need to bind `T` too.

To handle these (frequently occurring cases), the encoding
of a the type of Eunoia program is calculated with respect
to its list of parameters, where the parameters that appear
free in the signature are bound as implicit. e.g.,
```lp
sequential symbol {|$evaluate_internal|}
  : Π [T : Set], El (T ⤳ {|eo::List|} ⤳ T);
```

Now consider encoding the rules of the (elaborated) program.
The raw encoding produces the following:
```lp
rule @{|$evaluate_internal|} _ $t
        (@{|eo::List::cons|} _ $tev {|eo::List::nil|})
    ↪ $tev;
```
The list of parameters `(T Type) (t T) (tev T)` given by the
Eunoia specification of `$evaluate_internal` provides some
type constraints which are utilized for resolution:
```lp
rule @{|$evaluate_internal|} T $t
        (@{|eo::List::cons|} T $tev {|eo::List::nil|})
    ↪ $tev;
```
During resolution, the wildcards of `$evaluate_internal`
and `eo::List::cons` generate metavariables:
  `?1 : Set` and `?2 : Set` resp.

Without the Eunoia type information, `lambdapi` would infer:
  `$t : El ?1`
  `$tev : El ?2`
and hence fail to provide type preservation because:
  `?lhs := $evaluate_internal ... : El ?1`
  `?rhs := $tev : El ?2`

The Eunoia parameters should introduce a pattern variable
`$T : Set` and constraints `$t : El $T`, `$tev : El $T`.

Then lambdapi should infer `?1 = $T` and `?2 = $T` and
produce the following output:
```lp
rule @{|$evaluate_internal|} $T $t
        (@{|eo::List::cons|} $T $tev {|eo::List::nil|})
    ↪ $tev;
```




----------
2026-01-23
----------

We can't do anything useful with lambdapi string literals
other than pattern match on them in rewrite rules.
So really, we need to identify `eo::String` with lists of lambdapi string literals.
Then we can implement `eo::len` by just taking the length of the list, etc.



Contemplating `eo::add`. Arithmetic literals. Overloading. etc.

In this declaration, see `eo::add`
```
(declare-parameterized-const concat ((n Int :implicit) (m Int :implicit))
  (-> (BitVec n) (BitVec m) (BitVec (eo::add n m)))
  :right-assoc-nil @bv_empty)
```
It is `eo::add [Int] [Int] n m : el Int`



Consider adopting the policy:
After `(declare-consts <numeral> Int)`, we introduce a
coercion `toInt : el (eo::Int -> Int)`. Hereinafter,
whenever we see an integer literal, we wrap in `toInt`.

Then we can do mixed `eo::add`:
```lambdapi
type (λ x : τ Int, {|eo::add|} (toInt 0) x);
```

See
```
(define $arith_eval_qsub ((U Type :implicit) (T Type :implicit) (x U) (y T))
  (eo::add (eo::to_q x) (eo::neg (eo::to_q y)))
)
```

See
```
(program $arith_eval_int_log_2_rec ((x Int))
  :signature (Int) Int
  (
  (($arith_eval_int_log_2_rec 1) 0)
  (($arith_eval_int_log_2_rec x) (eo::add 1 ($arith_eval_int_log_2_rec (eo::zdiv x 2))))
  )
)
```




-----------------
# 2026-01-06
-----------------
Still thinking about overloading.
We could just have a constructor
  `const : string -> (a : set) -> el a`.
But this defeats the need for actually declaring constants
using `symbol` in the first place.

Also, looking at the `ethos` tests, it seems like
definitions (aka. macros) can be overloaded too.

In general, we disambiguate whilst desugaring applications.
  `(f t1 ... tn)`
According to the documentation, we choose the first symbol
that results in a well-typed term (which could be a partial
application).
  However, I can envision some scenarios in which we cannot
tell that the resulting term is well-typed due to the
presence of program applications in terms/types.
  For example:

  `(x Int) (y Real)`
  `(+ x y) : $arith_typeunion Int Real`
  `(+ x y) : Real`

  f1:`f : Int -> Int -> Int`
  f2:`f : Int -> Real -> Int`
  t:`(f 1 (+ x y))`

We want to choose `f2` because the type of `(+ x y)` is
`Real` modulo rewriting, but we cannot know this in OCaml.
So, we should use Dedukti/LambdaPi as our typechecker and
rewriting engine during translation. We add to the signature
as we go, making queries occasionally.

So how do we build our signature? We can use lambdapi
symbols, but we need to 'index' them in case there is
more than one. So either every symbol needs to have an
index on its name or in its type, e.g.,
  `+_0 : t ` or `+ (n : Int) : t(n) `
Name is probably easier, because otherwise each symbol's
type/definition would be dependent on the `n : Int`.
We just add primes to the names.

Then, perhaps all of the 'stateful' information can be
held in the lambdapi signature. i.e., types, attributes.
No, forget about attributes right now. Also, we want to
avoid parsing LambdaPi stuff, so we don't want to ask for
complex information when querying LP. Just a yes/no.
  "is `t` well-typed?" or "does `x` have type `t`?".

Using LP to actually compute some result would require us
to feed the result back into LambdaPi, which we don't want.







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
