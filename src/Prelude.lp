require open Stdlib.HOL Stdlib.Bool;

require open Stdlib.List;
require open Stdlib.String;
require Stdlib.Pos as Bin;
require open Stdlib.Comp;
require open Stdlib.Z;
require open Stdlib.Q;

// the set of all Eunoia {|eo::Type|}s.
symbol {|eo::Type|} : Set;
rule τ {|eo::Type|} ↪ Set;

// dependent arrow {|eo::Type|} for quoting
symbol ⤳d (T : τ {|eo::Type|}) : τ (T ⤳ {|eo::Type|}) → τ {|eo::Type|};
notation ⤳d infix right 5;
rule τ ($T ⤳d $F) ↪ (Π x : τ $T, τ ($F x));

// higher-order application (eo::_).
symbol APP [a b] : τ (a ⤳ b) → τ a → τ b;

// inlined typechecking (eo::as).
symbol {|eo::as|} (a : Set) (x : τ a) : τ a;
rule {|eo::as|} _ $x ↪ $x;

// Core types - use Stdlib types where possible
symbol Bool : Set;
rule τ Bool ↪ 𝔹;

symbol FAIL [a] : τ a;

// type-level ite.
sequential symbol ?? : 𝔹 → Set → Set → Set;
rule ?? _ $x $x ↪ $x
with ?? true $x _ ↪ $x
with ?? _ _ $y ↪ $y;

// `(eo::ite t1 t2 t3)`: Returns `t2` if `t1` is `true`, `t3` if `t1` is `false`,
// and is not evaluated otherwise. Note that the branches of this term are
// only evaluated if they are the return term.
sequential symbol {|eo::ite|} [U T : Set] (b : τ Bool) : τ (U ⤳ T ⤳ (?? b U T));
rule {|eo::ite|} true $x _ ↪ $x
with {|eo::ite|} false _ $y ↪ $y;


// --- logical operators. ---
sequential symbol {|eo::and|} : τ (Bool ⤳ Bool ⤳ Bool);
// boolean and conjunction.
rule {|eo::and|} true true ↪ true
with {|eo::and|} _ _ ↪ false;

// --- eo::or ---
sequential symbol {|eo::or|} : τ (Bool ⤳ Bool ⤳ Bool);
// boolean disjunction.
rule {|eo::or|} true _ ↪ true
with {|eo::or|} _ true ↪ true
with {|eo::or|} false false ↪ false;

// --- eo::not ---
sequential symbol {|eo::not|} : τ (Bool ⤳ Bool);
// boolean negation.
rule {|eo::not|} true ↪ false
with {|eo::not|} false ↪ true;

// --- eo::xor ---
sequential symbol {|eo::xor|} : τ (Bool ⤳ Bool ⤳ Bool);
// boolean xor.
rule {|eo::xor|} true true ↪ false
with {|eo::xor|} true false ↪ true
with {|eo::xor|} false true ↪ true
with {|eo::xor|} false false ↪ false;


// `(eo::requires t1 t2 t3)`: Returns `t3` if `(eo::is_eq t1 t2)` evaluates to
// `true`, and is not evaluated otherwise. In the case this operator
// evaluates, it may be the case that `t3` is non-ground.
sequential symbol {|eo::requires|} [T U V]
  (x : τ T) (y : τ U) (z : τ V) : τ V;
rule {|eo::requires|} $x $x $z ↪ $z
// Also reduce when second arg is literal `true` (for type-level guards)
with {|eo::requires|} _ true $z ↪ $z;

symbol {|eo::String|}  : Set;
rule τ {|eo::String|} ↪ String;

symbol {|eo::Int|} : Set;
rule τ {|eo::Int|} ↪ ℤ;

symbol {|eo::Rat|} : Set;
rule τ {|eo::Rat|} ↪ ℚ;

//// subset relation.
//symbol ⪽ : Set → Set → 𝔹;
//notation ⪽ infix 5;
//rule $x ⪽ $x ↪ true;

//rule {|eo::Int|} ⪽ {|eo::Rat|} ↪ true;
//rule {|eo::Rat|} ⪽ {|eo::Int|} ↪ false;

//sequential symbol cases : 𝔹 → 𝔹 → Set → Set → Set;
//rule cases true _ $x _ ↪ $x
//with cases _ true _ $y ↪ $y;


symbol ⊍ : Set → Set → Set; notation ⊍ infix 5;
rule τ ({|eo::Int|} ⊍ {|eo::Int|}) ↪ τ {|eo::Int|}
with τ ({|eo::Int|} ⊍ {|eo::Rat|}) ↪ τ {|eo::Rat|}
with τ ({|eo::Rat|} ⊍ {|eo::Int|}) ↪ τ {|eo::Rat|}
with τ ({|eo::Rat|} ⊍ {|eo::Rat|}) ↪ τ {|eo::Rat|};


symbol {|eo::mkrat|} : ℤ → ℤ → ℚ;

symbol ⊥ : Set;



// Eunoia builtins
// `(eo::is_ok t)`: If `t` is ground, this returns true if `t` is a value, and
// false otherwise. If `t` is not ground, it does not evaluate.
sequential symbol {|eo::is_ok|} [T : Set]: τ (T ⤳ Bool);



// `(eo::eq t1 t2)`: If `t1` and `t2` are ground values, this returns `true` if
// `t1` is (syntactically) equal to `t2` and `false` otherwise. If either
// `t1` or `t2` is non-ground, it does not evaluate.
sequential symbol {|eo::eq|} [T : Set] [S : Set] : τ (T ⤳ S ⤳ Bool);
rule {|eo::eq|} $x $x ↪ true
with {|eo::eq|} _ _ ↪ false;



// `(eo::is_eq t1 t2)`: Equivalent to `(eo::ite (eo::and (eo::is_ok t) (eo::is_ok s)) (eo::eq s t) false)`.
sequential symbol {|eo::is_eq|} [T1 T2]: τ (T1 ⤳ T2 ⤳ Bool);
// `(eo::hash t1)`: If `t1` is a value, this returns a numeral that is unique
// to `t1`.
sequential symbol {|eo::hash|} [T : Set]: τ (T ⤳ {|eo::Int|});

// ---- types, variables, names. ----
// `(eo::typeof t1)`: If `t1` is a value, this returns the {|eo::Type|} of `t1` if its type is ground.
sequential symbol {|eo::typeof|} [T : Set]: τ (T ⤳ {|eo::Type|});
rule {|eo::typeof|} [$T] _ ↪ $T;

// `(eo::var t1 t2)`: If `t1` is a string value and `t2` is a ground {|eo::Type|}, this
// returns the variable whose name is `t1` and whose {|eo::Type|} is `t2`.
sequential symbol {|eo::var|} [T : Set]: τ ({|eo::String|} ⤳ T ⤳ T);

// `(eo::nameof t1)`: If `t1` is a ground constant or variable, this returns
// the name of `t1`, i.e. the string corresponding to the symbol it was
// declared with.
sequential symbol {|eo::nameof|} [T : Set]: τ (T ⤳ {|eo::String|});
rule {|eo::nameof|} ({|eo::var|} $s _) ↪ $s;

// `(eo::cmp t1 t2)`: Equivalent to `(eo::is_neg (eo::add (eo::neg (eo::hash t1)) (eo::hash t2)))`.
// Note that this method corresponds to an arbitrary total order on terms.
sequential symbol {|eo::cmp|} [T : Set] [U : Set]: τ (T ⤳ U ⤳ Bool);

// `(eo::is_var t)`: Equivalent to `(eo::is_eq (eo::var (eo::nameof t) (eo::{|eo::Type|}of t)) t)`.
sequential symbol {|eo::is_var|} [T : Set]: τ (T ⤳ Bool);
rule {|eo::is_var|} ({|eo::var|} _ _) ↪ true
with {|eo::is_var|} _          ↪ false;

// `(eo::is_z t)`: Equivalent to `(eo::is_eq (eo::to_z t) t)`.
sequential symbol {|eo::is_z|} [T : Set]: τ (T ⤳ Bool);
rule {|eo::is_z|} [{|eo::Int|}] _ ↪ true
with {|eo::is_z|} _ ↪ false;

// ---- conversion operators. ----
// `(eo::to_z t1)`: Converts `t1` to an integer.
// - If `t1` is a numeral value, return `t1`.
// - If `t1` is a rational value, return the numeral value corresponding to the floor of `t1`.
// - If `t1` is a binary value, this returns the numeral value corresponding to `t1`.
// - If `t1` is a string value of length one, this returns the code point of its character.
sequential symbol {|eo::to_z|} [T : Set]: τ (T ⤳ {|eo::Int|});

// `(eo::to_q t1)`: Converts `t1` to a rational.
// - If `t1` is a rational value, return `t1`.
// - If `t1` is a numeral value, this returns the (integral) rational value that is equivalent to `t1`.
sequential symbol {|eo::to_q|} [T : Set]: τ (T ⤳ {|eo::Rat|});

// `(eo::to_bin t1 t2)`: Converts `t2` to a binary value of bitwidth `t1`.
// - If `t1` is a 32-bit numeral value and `t2` is a binary value, this
//   returns a binary value whose value is `t2` and whose bitwidth is `t1`.
// - If `t1` is a 32-bit numeral value and `t2` is a non-negative numeral
//   value, return the binary value whose value is `t2` (modulo `2^t1`) and
//   whose bitwidth is `t1`.
sequential symbol {|eo::to_bin|} [T : Set]: τ ({|eo::Int|} ⤳ T ⤳ T);

// `(eo::to_str t1)`: Converts `t1` to a string.
// - If `t1` is a string value, return `t1`.
// - If `t1` is a numeral value specifying a code point from Unicode planes
//   `0-2` (i.e. a numeral between `0` and `196607`), return the string of
//   length one whose character has code point `t1`.
// - If `t1` is a rational or binary value, return the string value
//   corresponding to the result of printing `t1`.
// - If `t1` is a hexadecimal value, return the string value corresponding
//   to the result of printing `t1`. This will use lowercase letters for
//   digits greater than `9`.
// - If `t1` is a decimal value, return the string value corresponding to
//   the result of printing `t1` as a rational.
sequential symbol {|eo::to_str|} [T : Set]: τ (T ⤳ {|eo::String|});


// ---- arithmetic. ----
// `(eo::add t1 t2)`:
// - If `t1` and `t2` are arithmetic values of the same category, then this
//   returns the addition of `t1` and `t2`.
// - If `t1` and `t2` are bitwise values of the same category and bitwidth,
//   this returns the binary value corresponding to their (unsigned) addition
//   modulo their bitwidth.
sequential symbol {|eo::add|} [T1 T2] : τ (T1 ⤳ T2 ⤳ (T1 ⊍ T2));
rule {|eo::add|} [{|eo::Int|}] [{|eo::Int|}] $i $j ↪ $i + $j
with {|eo::add|} [{|eo::Rat|}] [{|eo::Rat|}] $x $y ↪ qadd $x $y;

// `(eo::mul t1 t2)`:
// - If `t1` and `t2` are arithmetic values of the same category, then this
//   returns the multiplication of `t1` and `t2`.
// - If `t1` and `t2` are bitwise values of the same category and bitwidth,
//   this returns the binary value corresponding to their (unsigned)
//   multiplication modulo their bitwidth.
sequential symbol {|eo::mul|} [T1 T2] : τ (T1 ⤳ T2 ⤳ (T1 ⊍ T2));
rule {|eo::mul|} [{|eo::Int|}] [{|eo::Int|}] $i $j ↪ $i * $j
with {|eo::mul|} [{|eo::Rat|}] [{|eo::Rat|}] $x $y ↪ qmul $x $y;

// `(eo::neg t1)`:
// - If `t1` is a arithmetic value, this returns the arithmetic negation of `t1`.
// - If `t1` is a binary value, this returns its (signed) arithmetic negation.
sequential symbol {|eo::neg|} [T : Set]: τ (T ⤳ T);
rule {|eo::neg|} [{|eo::Int|}] $i ↪ — $i;

// `(eo::qdiv t1 t2)`: If `t1` and `t2` are values of the same category and `t2`
// is non-zero, then this returns the rational division of `t1` and `t2`.
sequential symbol {|eo::qdiv|} [T1 T2]: τ (T1 ⤳ T2 ⤳ {|eo::Rat|});
rule {|eo::qdiv|} [{|eo::Int|}] [{|eo::Int|}] $i $j ↪ {|eo::qdiv|} ({|eo::to_q|} $i) ({|eo::to_q|} $j)
with {|eo::qdiv|} [{|eo::Rat|}] [{|eo::Rat|}] $x $y ↪ {|eo::qdiv|} $x $y;

// `(eo::zdiv t1 t2)`:
// - If `t1` and `t2` are numeral values and `t2` is non-zero, then this
//   returns the integer division (floor) of `t1` and `t2`.
// - If `t1` and `t2` are bitwise values of the same category and bitwidth,
//   then this returns their (total, unsigned) division, where division by
//   zero returns the max unsigned value.
sequential symbol {|eo::zdiv|} [T : Set]: τ (T ⤳ T ⤳ T);
//rule {|eo::zdiv|} [{|eo::Int|}] $i $j ↪ Int.zdiv $i $j
//with {|eo::zdiv|} [{|eo::Rat|}] $x $y ↪ Int.zdiv ({|eo::to_z|} $x) ({|eo::to_z|} $y);

// `(eo::zmod t1 t2)`:
// - If `t1` and `t2` are numeral values and `t2` is non-zero, then this
//   returns the integer remainder of `t1` and `t2`.
// - If `t1` and `t2` are bitwise values of the same category and bitwidth,
//   then this returns their (total, unsigned) remainder, where remainder by
//   zero returns `t1`.
sequential symbol {|eo::zmod|} [T : Set]: τ (T ⤳ T ⤳ T);
//rule {|eo::zmod|} [{|eo::Int|}] $i $j ↪ Int.zmod $i $j;

// `(eo::is_neg t1)`: If `t1` is an arithmetic value, this returns `true` if `t1`
// is strictly negative and `false` otherwise. Otherwise, this operator is not
// evaluated.
sequential symbol {|eo::is_neg|} [T : Set]: τ (T ⤳ Bool);
rule {|eo::is_neg|} [{|eo::Int|}] $i ↪ isZneg $i;

// `(eo::gt t1 t2)`: Equivalent to `(eo::is_neg (eo::add (eo::neg t1) t2))`.
sequential symbol {|eo::gt|} [T1 : Set] [T2 : Set]: τ (T1 ⤳ T2 ⤳ Bool);
rule {|eo::gt|} [{|eo::Int|}] [{|eo::Int|}] $i $j ↪ isGt ($i ≐ $j);


// ---- bitvectors. ----
// `(eo::len t1)`:
// - Binary length (bitwidth) if `t1` is a binary value.
// - String length if `t1` is a string value.
sequential symbol {|eo::len|} [T : Set]: τ (T ⤳ {|eo::Int|});

// `(eo::concat t1 t2)`:
// - The concatenation of bits if `t1` and `t2` are binary values.
// - The concatenation of strings if `t1` and `t2` are string values.
sequential symbol {|eo::concat|} [T : Set]: τ (T ⤳ T ⤳ T);

// `(eo::extract t1 t2 t3)`:
// - If `t1` is a binary value and `t2` and `t3` are numeral values, this
//   returns the binary value corresponding to the bits in `t1` from position
//   `t2` through `t3` if `0<=t2`, or the empty binary value otherwise.
// - If `t1` is a string value and `t2` and `t3` are numeral values, this
//   returns the string value corresponding to the characters in `t1` from
//   position `t2` through `t3` inclusive if `0<=t2`, or the empty string value
//   otherwise.
// Made polymorphic to accept both {|eo::Int|} and Int index types
sequential symbol {|eo::extract|} [T I1 I2 : Set]: τ (T ⤳ I1 ⤳ I2 ⤳ T);

// `(eo::find t1 t2)`: If `t1` and `t2` are string values, this returns a
// numeral value corresponding to the first index (left to right) where `t2`
// occurs as a substring of `t1`, or the numeral value `-1` otherwise.
sequential symbol {|eo::find|} : τ ({|eo::String|} ⤳ {|eo::String|} ⤳ {|eo::Int|});


// ---- list operators. ----
// `(eo::nil f T)`: If `f` is a right associative operator and `T` is a ground
// {|eo::Type|}, return its nil terminator. If `f` has a parametric nil terminator,
// return the terminator is specialized for `T`.
sequential symbol {|eo::nil|} [T1 T2]
    (f : τ (T1 ⤳ T2 ⤳ T2))
    (T : τ {|eo::Type|}) : τ T;

// `(eo::cons f t1 t2)`: If `t2` is an `f`-list, then this returns the term `(f t1 t2)`.
sequential symbol {|eo::cons|} [U : Set] [T : Set] :
	τ ((U ⤳ T ⤳ T) ⤳ U ⤳ T ⤳ T);
rule {|eo::cons|} $f $x (APP (APP $f $y) $ys)
  ↪ APP (APP $f $x) (APP (APP $f $y) $ys)
with {|eo::cons|} [_] [$T] $f $x $xs
  ↪ {|eo::requires|} $xs ({|eo::nil|} $f $T) (APP (APP $f $x) $xs);

sequential  symbol {|eo::fold|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (list T1 ⤳ T2);
rule {|eo::fold|} $f ($x ⸬ $xs) ↪ APP (APP $f $x) ({|eo::fold|} $f $xs)
with {|eo::fold|} [_] [$T2] $f □          ↪ {|eo::nil|} $f $T2;

sequential symbol {|eo::unfold|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ list T1);
rule {|eo::unfold|} $f (APP (APP $f $x) $xs) ↪ $x ⸬ ({|eo::unfold|} $f $xs)
with {|eo::unfold|} [_] [$T2] $f $z ↪ {|eo::requires|} $z ({|eo::nil|} $f $T2) □;

// `(eo::list_concat f t1 t2)`: If `t1` is an `f`-list with children
// `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`, this
// returns `(f t11 ... t1n t21 ... t2m)` if `n+m>0` and `nil` otherwise.
// Otherwise, this operator does not evaluate.
sequential symbol {|eo::list_concat|}
  [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) :
  τ (T2 ⤳ T2 ⤳ T2);
rule {|eo::list_concat|} $f $xs $ys ↪ {|eo::fold|} $f ({|eo::unfold|} $f $xs ++ {|eo::unfold|} $f $ys);



// `(eo::list_len f t)`: If `t` is an `f`-list with children `t1 ... tn`, then
// this returns `n`.
symbol length [a] : 𝕃 a → ℤ;
rule length □ ↪ 0
with length (_ ⸬ $xs) ↪ 1 + length $xs;

sequential symbol {|eo::list_len|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) :
  τ (T2 ⤳ {|eo::Int|});
rule {|eo::list_len|} $f $xs ↪ length ({|eo::unfold|} $f $xs);

// `(eo::list_nth f t1 t2)`: If `t1` is `(f s0 ... s{n-1})` and `t2` is a numeral
// value such that `0<=t2<n`, then this returns `s_{t2}`. Otherwise, this
// operator does not evaluate.
sequential symbol nth [a] : 𝕃 a → ℤ → τ a;
rule nth ($x ⸬ _) 0 ↪ $x
with nth (_ ⸬ $xs) $n ↪ nth $xs ($n + -1);

sequential symbol {|eo::list_nth|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ {|eo::Int|} ⤳ T1);
rule {|eo::list_nth|} $f $xs $i ↪ nth ({|eo::unfold|} $f $xs) $i;

// `(eo::list_find f t1 t2)`: If `t1` is `(f s0 ... s{n-1})`, then this returns
// the smallest numeral value `i` such that `t2` is syntactically equal to
// `si`, or `-1` if no such `si` can be found. Otherwise, this operator does
// not evaluate.
symbol index [a] : τ a → 𝕃 a → ℤ;
rule index $x ($y ⸬ $xs) ↪
  {|eo::ite|} ({|eo::eq|} $x $y) 0 (1 + index $x $xs);

sequential symbol {|eo::list_mem|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T1 ⤳ Bool);
rule {|eo::list_mem|} [$T1] [_] $f $xs $x ↪ ∈ ({|eo::eq|} [$T1] [$T1]) $x ({|eo::unfold|} $f $xs);

sequential symbol {|eo::list_find|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T1 ⤳ {|eo::Int|});
rule {|eo::list_find|} $f $xs $x
  ↪ {|eo::ite|} ({|eo::list_mem|} $f $xs $x) (index $x ({|eo::unfold|} $f $xs)) -1;

// `(eo::list_rev f t1)`: If `t1` is an `f`-list with children `t11 ... t1n`,
// then this returns `(f t1n ... t11)`.
sequential symbol {|eo::list_rev|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2);
rule {|eo::list_rev|} $f $xs ↪ {|eo::fold|} $f (rev ({|eo::unfold|} $f $xs));

// `(eo::list_erase f t1 t2)`:
// If `t1` is an `f`-list, then this returns the
// result of removing the first occurrence of `t2` from `t1` if it exists.
// Returns `t1` unchanged if it does not contain `t2`.
symbol rem [a] : τ a → 𝕃 a → 𝕃 a;
rule rem _ □ ↪ □
with rem $x ($y ⸬ $ys)
  ↪ {|eo::ite|} ({|eo::eq|} $x $y) $ys ($y ⸬ rem $x $ys);

sequential symbol {|eo::list_erase|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T1 ⤳ T2);
rule {|eo::list_erase|} $f $xs $x ↪ {|eo::fold|} $f (rem $x ({|eo::unfold|} $f $xs));

// `(eo::list_erase_all f t1 t2)`: If `t1` is an `f`-list, then this returns the
// result of removing all occurrences of `t2` from `t1`, where the remaining
// elements are kept in order. Returns `t1` unchanged if it does not
// contain `t2`.
sequential symbol {|eo::list_erase_all|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T1 ⤳ T2);
rule {|eo::list_erase_all|} $f $xs $x
  ↪ let ys ≔ {|eo::unfold|} $f $xs in
    let ys' ≔ filter (λ y, {|eo::not|} ({|eo::eq|} $x y)) ys in
    {|eo::fold|} $f ys';

// `(eo::list_setof f t1)`: If `t1` is an `f`-list with children `t11 ... t1n`,
// this returns the `f`-list obtained by dropping each element from this list
// beyond the first occurrence. Note that the remaining elements are kept in
// order.

// Helper: undup that keeps FIRST occurrence (stdlib's undup keeps last)
// Eunoia spec says list_setof should keep first occurrence
symbol undup_first [a] : 𝕃 a → 𝕃 a;
rule undup_first □ ↪ □
with undup_first ($x ⸬ $xs) ↪
  $x ⸬ undup_first (filter (λ y, {|eo::not|} ({|eo::eq|} $x y)) $xs);

sequential symbol {|eo::list_setof|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2);
rule {|eo::list_setof|} $f $xs
  ↪ let ys ≔ {|eo::unfold|} $f $xs in
    {|eo::fold|} $f (undup_first ys);

// Helper: count occurrences of an element in a list
symbol count_occ [a] : τ a → 𝕃 a → ℤ;
rule count_occ _ □ ↪ 0
with count_occ $x ($y ⸬ $ys) ↪ {|eo::ite|} ({|eo::eq|} $x $y) (1 + count_occ $x $ys) (count_occ $x $ys);



// Helper: check if for all elements of first list, their count in first list
// is <= their count in second list
symbol minclude_check [a] : 𝕃 a → 𝕃 a → 𝕃 a → 𝔹;
rule minclude_check _ □ _ ↪ true
with minclude_check $full ($x ⸬ $xs) $ys ↪
  {|eo::and|} ({|eo::not|} (isGt (count_occ $x $full ≐ count_occ $x $ys)))
      (minclude_check $full $xs $ys);


// `(eo::list_minclude f t1 t2)`: (Multiset inclusion) If `t1` is an `f`-list
// with children `t11 ... t1n` and `t2` is an `f`-list with children
// `t21 ... t2m`, then this returns true if each unique element in
// `t11 ... t1n` occurs with the greater than or equal multiplicity in
// `t21 ... t2m`. Note that order of the elements does not matter.
sequential symbol {|eo::list_minclude|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2 ⤳ Bool);
rule {|eo::list_minclude|} $f $xs $ys ↪
  let xs' ≔ {|eo::unfold|} $f $xs in
  let ys' ≔ {|eo::unfold|} $f $ys in
  minclude_check xs' xs' ys';


// `(eo::list_meq f t1 t2)`: (Multiset equal) Equivalent to
// `(eo::and (eo::list_minclude f t1 t2) (eo::list_minclude f t2 t1))`.
sequential symbol {|eo::list_meq|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2 ⤳ Bool);
rule {|eo::list_meq|} $f $xs $ys ↪ {|eo::and|} ({|eo::list_minclude|} $f $xs $ys) ({|eo::list_minclude|} $f $ys $xs);



// `(eo::list_diff f t1 t2)`: (Difference) If `t1` is an `f`-list with children
// `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`, this
// returns the result of erasing elements of `t11 ... t1n` that occur in
// `t21 ... t2m` where multiplicity is considered. In detail, for each
// `i = 1, ..., n`, if `t1i` occurs in `t21 ... t2m`, we remove one copy of
// it from that list. Otherwise if `t1i` does not occur in `t21 ... t2m`,
// we append it to the final result.
// Helper: diff_aux xs ys returns (result, remaining_ys)
// where result contains elements of xs not in ys (with multiplicity)
symbol diff_aux [a] : 𝕃 a → 𝕃 a → 𝕃 a;
rule diff_aux □ _ ↪ □
with diff_aux ($x ⸬ $xs) $ys ↪
  {|eo::ite|} (∈ {|eo::eq|} $x $ys)
      (diff_aux $xs (rem $x $ys))
      ($x ⸬ diff_aux $xs $ys);

sequential symbol {|eo::list_diff|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2 ⤳ T2);
rule {|eo::list_diff|} $f $xs $ys ↪
  {|eo::fold|} $f (diff_aux ({|eo::unfold|} $f $xs) ({|eo::unfold|} $f $ys));
// `(eo::list_inter f t1 t2)`: (Intersection) If `t1` is an `f`-list with
// children `t11 ... t1n` and `t2` is an `f`-list with children
// `t21 ... t2m`, this returns the result of erasing elements of `t11 ... t1n`
// that do not occur in `t21 ... t2m` where multiplicity is considered. In
// detail, for each `i = 1, ..., n`, if `t1i` occurs in `t21 ... t2m`, we
// erase one copy of it from that list and append it to the final result.
// Helper: inter_aux xs ys returns elements of xs that are also in ys (with multiplicity)
symbol inter_aux [a] : 𝕃 a → 𝕃 a → 𝕃 a;
rule inter_aux □ _ ↪ □
with inter_aux ($x ⸬ $xs) $ys ↪
  {|eo::ite|} (∈ {|eo::eq|} $x $ys)
      ($x ⸬ inter_aux $xs (rem $x $ys))
      (inter_aux $xs $ys);

sequential symbol {|eo::list_inter|} [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2 ⤳ T2);
rule {|eo::list_inter|} $f $xs $ys ↪
  {|eo::fold|} $f (inter_aux ({|eo::unfold|} $f $xs) ({|eo::unfold|} $f $ys));


// `(eo::list_singleton_elim f t1)`: (Singleton elimination) If `t1` is an
// `f`-list containing a single child `t11`, this returns `t11`. All other
// `f`-lists `t1` are returned unchanged. Otherwise, this operator does not
// evaluate.
// Note: In Eunoia, this can return T1 when singleton but T2 otherwise.
// For our encoding, we restrict to the common case where T1 = T2.
sequential symbol {|eo::list_singleton_elim|} [T] (f : τ (T ⤳ T ⤳ T)) : τ (T ⤳ T);
// Helper to check if unfolded list is a singleton and return element or original
sequential symbol singleton_elim_aux [T] : τ (T ⤳ T ⤳ T) → 𝕃 T → τ T → τ T;
// If the list has exactly one element, return that element
// Otherwise return the original term
rule singleton_elim_aux _ ($x ⸬ □) _ ↪ $x
with singleton_elim_aux _ _ $orig ↪ $orig;

rule {|eo::list_singleton_elim|} $f $xs ↪ singleton_elim_aux $f ({|eo::unfold|} $f $xs) $xs;

// eo::List, eo::List::cons, eo::List::nil
symbol {|eo::List|} : τ {|eo::Type|};
sequential symbol {|eo::List::nil|} : τ {|eo::List|}; symbol ∎ ≔ {|eo::List::nil|};
sequential symbol {|eo::List::cons|} [T : Set]: τ (T ⤳ {|eo::List|} ⤳ {|eo::List|});

// nil rule for eo::List::cons
rule {|eo::nil|} {|eo::List::cons|} {|eo::List|} ↪ {|eo::List::nil|};


// ---- Additional type checking predicates ----

// `(eo::is_q t)`: Equivalent to `(eo::is_eq (eo::to_q t) t)`.
sequential symbol {|eo::is_q|} [T : Set]: τ (T ⤳ Bool);
rule {|eo::is_q|} [{|eo::Rat|}] _ ↪ true
with {|eo::is_q|} _ ↪ false;

// `(eo::is_bin t)`: Equivalent to `(eo::is_eq (eo::to_bin (eo::len t) t) t)`.
// Returns true if t is a binary (bitvector) value.
sequential symbol {|eo::is_bin|} [T : Set]: τ (T ⤳ Bool);
// Note: actual bitvector type checking requires knowing the BitVec type
// For now, we provide a placeholder that theories can extend with rules
rule {|eo::is_bin|} _ ↪ false;

// `(eo::is_bool t)`: Returns true if t is a boolean value.
sequential symbol {|eo::is_bool|} [T : Set]: τ (T ⤳ Bool);
rule {|eo::is_bool|} [Bool] true ↪ true
with {|eo::is_bool|} [Bool] false ↪ true
with {|eo::is_bool|} _ ↪ false;

// `(eo::is_str t)`: Equivalent to `(eo::is_eq (eo::to_str t) t)`.
// Returns true if t is a string value.
sequential symbol {|eo::is_str|} [T : Set]: τ (T ⤳ Bool);
rule {|eo::is_str|} [{|eo::String|}] _ ↪ true
with {|eo::is_str|} _ ↪ false;

// ---- Datatype introspection ----

// `(eo::dt_constructors D)`: If D is a datatype, returns the list of constructors for D.
// This is a builtin that requires datatype information at runtime.
sequential symbol {|eo::dt_constructors|} : τ ({|eo::Type|} ⤳ {|eo::List|});

// `(eo::dt_selectors c)`: If c is a constructor, returns the list of selectors for c.
sequential symbol {|eo::dt_selectors|} [T : Set]: τ (T ⤳ {|eo::List|});

// ---- Comparison and ordering ----

// `(eo::compare t1 t2)`: Compares two terms and returns -1, 0, or 1.
// This is similar to eo::cmp but returns an integer instead of a boolean.
sequential symbol {|eo::compare|} [T U : Set]: τ (T ⤳ U ⤳ {|eo::Int|});

// ---- Meta/quoting operators ----

// `(eo::define ((x t)) s)`: Local binding, equivalent to let x = t in s.
// This is typically handled during elaboration, but we provide a symbol for completeness.
sequential symbol {|eo::define|} [T U : Set]: τ (T ⤳ U ⤳ U);
rule {|eo::define|} $t $body ↪ $body;

// `(eo::quote t)`: Returns t unevaluated.
sequential symbol {|eo::quote|} [T : Set]: τ (T ⤳ T);
rule {|eo::quote|} $t ↪ $t;

// `(eo::self t)`: Returns the current program being evaluated.
// This is a meta-operation used for recursive program definitions.
sequential symbol {|eo::self|} [T : Set]: τ T;
