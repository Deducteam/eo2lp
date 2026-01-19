require open Stdlib.HOL Stdlib.Bool;

require Stdlib.List as L;
require Stdlib.String as Str;
require Stdlib.Pos as Bin;
require open Stdlib.Comp;
require Stdlib.Z as Int;

require prelude.Q as Rat;

// the set of all Eunoia types.
symbol Type : Set;
rule τ Type ↪ Set;

// dependent arrow type for quoting
symbol ⤳d (T : τ Type) : τ (T ⤳ Type) → τ Type;
notation ⤳d infix right 5;
rule τ ($T ⤳d $F) ↪ (Π x : τ $T, τ ($F x));

// higher-order application.
symbol ⋅ [a b] : τ (a ⤳ b) → τ a → τ b;
notation ⋅ infix left 5;

// inlined typechecking.
symbol _as (a : Set) (x : τ a) : τ a;
rule _as _ $x ↪ $x;

// Core types - use Stdlib types where possible
symbol Bool : Set;
rule τ Bool ↪ 𝔹;

symbol <str> : Set;
rule τ <str> ↪ Str.String;

symbol <int> : Set;
rule τ <int> ↪ Int.ℤ;

symbol <rat> : Set;
rule τ <rat> ↪ Rat.ℚ;

// just !arith_typeunion but for the eo.add, etc.
// Note: we need rules for both <int>/<rat> (Prelude types) and any aliases defined
// in theory files. Since we can't predict all aliases, theories that define
// type aliases like `Int ≔ <int>` should also add corresponding ⊍ rules.
symbol ⊍ : Set → Set → Set; notation ⊍ infix 5;
rule <int> ⊍ <int> ↪ <int>
with <rat> ⊍ <rat> ↪ <rat>
with <rat> ⊍ <int> ↪ <rat>
with <int> ⊍ <rat> ↪ <rat>;

symbol ⊥ : Set;

symbol ?? : 𝔹 → Set → Set → Set;
rule ?? _ $x $x ↪ $x
with ?? true $x _ ↪ $x
with ?? false _ $y ↪ $y;



// Eunoia builtins
// `(is_ok t)`: If `t` is ground, this returns true if `t` is a value, and
// false otherwise. If `t` is not ground, it does not evaluate.
sequential symbol is_ok [T : Set]: τ (T ⤳ Bool);

// `(ite t1 t2 t3)`: Returns `t2` if `t1` is `true`, `t3` if `t1` is `false`,
// and is not evaluated otherwise. Note that the branches of this term are
// only evaluated if they are the return term.
sequential symbol ite [U T : Set] (b : τ Bool) : τ (U ⤳ T ⤳ (?? b U T));
rule ite true $x _ ↪ $x
with ite false _ $y ↪ $y;

// `(eq t1 t2)`: If `t1` and `t2` are ground values, this returns `true` if
// `t1` is (syntactically) equal to `t2` and `false` otherwise. If either
// `t1` or `t2` is non-ground, it does not evaluate.
sequential symbol eq [T : Set] [S : Set] : τ (T ⤳ S ⤳ Bool);
rule eq $x $x ↪ true
with eq _ _ ↪ false;

// `(requires t1 t2 t3)`: Returns `t3` if `(is_eq t1 t2)` evaluates to
// `true`, and is not evaluated otherwise. In the case this operator
// evaluates, it may be the case that `t3` is non-ground.
sequential symbol requires [T U V]
  (x : τ T) (y : τ U) (z : τ V) : τ V;
rule requires $x $x $z ↪ $z;

// `(is_eq t1 t2)`: Equivalent to `(ite (and (is_ok t) (is_ok s)) (eq s t) false)`.
sequential symbol is_eq [T1 T2]: τ (T1 ⤳ T2 ⤳ Bool);
// `(hash t1)`: If `t1` is a value, this returns a numeral that is unique
// to `t1`.
sequential symbol hash [T : Set]: τ (T ⤳ <int>);

// ---- types, variables, names. ----
// `(typeof t1)`: If `t1` is a value, this returns the type of `t1` if its
// type is ground.
sequential symbol typeof [T : Set]: τ (T ⤳ Type);
rule typeof [$T] _ ↪ $T;

// `(var t1 t2)`: If `t1` is a string value and `t2` is a ground type, this
// returns the variable whose name is `t1` and whose type is `t2`.
sequential symbol var [T : Set]: τ (<str> ⤳ T ⤳ T);

// `(nameof t1)`: If `t1` is a ground constant or variable, this returns
// the name of `t1`, i.e. the string corresponding to the symbol it was
// declared with.
sequential symbol nameof [T : Set]: τ (T ⤳ <str>);
rule nameof (var $s _) ↪ $s;

// `(cmp t1 t2)`: Equivalent to `(is_neg (add (neg (hash t1)) (hash t2)))`.
// Note that this method corresponds to an arbitrary total order on terms.
sequential symbol cmp [T : Set] [U : Set]: τ (T ⤳ U ⤳ Bool);

// `(is_var t)`: Equivalent to `(is_eq (var (nameof t) (typeof t)) t)`.
sequential symbol is_var [T : Set]: τ (T ⤳ Bool);
rule is_var (var _ _) ↪ true
with is_var _          ↪ false;

// `(is_z t)`: Equivalent to `(is_eq (to_z t) t)`.
sequential symbol is_z [T : Set]: τ (T ⤳ Bool);
rule is_z [<int>] _ ↪ true
with is_z _ ↪ false;

// ---- conversion operators. ----
// `(to_z t1)`: Converts `t1` to an integer.
// - If `t1` is a numeral value, return `t1`.
// - If `t1` is a rational value, return the numeral value corresponding to the floor of `t1`.
// - If `t1` is a binary value, this returns the numeral value corresponding to `t1`.
// - If `t1` is a string value of length one, this returns the code point of its character.
sequential symbol to_z [T : Set]: τ (T ⤳ <int>);

// `(to_q t1)`: Converts `t1` to a rational.
// - If `t1` is a rational value, return `t1`.
// - If `t1` is a numeral value, this returns the (integral) rational value that is equivalent to `t1`.
sequential symbol to_q [T : Set]: τ (T ⤳ <rat>);

// `(to_bin t1 t2)`: Converts `t2` to a binary value of bitwidth `t1`.
// - If `t1` is a 32-bit numeral value and `t2` is a binary value, this
//   returns a binary value whose value is `t2` and whose bitwidth is `t1`.
// - If `t1` is a 32-bit numeral value and `t2` is a non-negative numeral
//   value, return the binary value whose value is `t2` (modulo `2^t1`) and
//   whose bitwidth is `t1`.
sequential symbol to_bin [T : Set]: τ (<int> ⤳ T ⤳ T);

// `(to_str t1)`: Converts `t1` to a string.
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
sequential symbol to_str [T : Set]: τ (T ⤳ <str>);


// --- logical operators. ---
sequential symbol and : τ (Bool ⤳ Bool ⤳ Bool);
// boolean and conjunction.
rule and true true ↪ true
with and true false ↪ false
with and false true ↪ false
with and false false ↪ false;

// --- eo::or ---
sequential symbol or : τ (Bool ⤳ Bool ⤳ Bool);
// boolean disjunction.
rule or true true ↪ true
with or true false ↪ true
with or false true ↪ true
with or false false ↪ false;

// --- eo::not ---
sequential symbol not : τ (Bool ⤳ Bool);
// boolean negation.
rule not true ↪ false
with not false ↪ true;

// --- eo::xor ---
sequential symbol xor : τ (Bool ⤳ Bool ⤳ Bool);
// boolean xor.
rule xor true true ↪ false
with xor true false ↪ true
with xor false true ↪ true
with xor false false ↪ false;

// ---- arithmetic. ----
// `(add t1 t2)`:
// - If `t1` and `t2` are arithmetic values of the same category, then this
//   returns the addition of `t1` and `t2`.
// - If `t1` and `t2` are bitwise values of the same category and bitwidth,
//   this returns the binary value corresponding to their (unsigned) addition
//   modulo their bitwidth.
sequential symbol add [T1 T2] : τ (T1 ⤳ T2 ⤳ (T1 ⊍ T2));
rule add [<int>] [<int>] $i $j ↪ $i Int.+ $j
with add [<rat>] [<rat>] $x $y ↪ Rat.qadd $x $y;

// `(mul t1 t2)`:
// - If `t1` and `t2` are arithmetic values of the same category, then this
//   returns the multiplication of `t1` and `t2`.
// - If `t1` and `t2` are bitwise values of the same category and bitwidth,
//   this returns the binary value corresponding to their (unsigned)
//   multiplication modulo their bitwidth.
sequential symbol mul [T1 T2] : τ (T1 ⤳ T2 ⤳ (T1 ⊍ T2));
rule mul [<int>] [<int>] $i $j ↪ $i Int.* $j
with mul [<rat>] [<rat>] $x $y ↪ Rat.qmul $x $y;

// `(neg t1)`:
// - If `t1` is a arithmetic value, this returns the arithmetic negation of `t1`.
// - If `t1` is a binary value, this returns its (signed) arithmetic negation.
sequential symbol neg [T : Set]: τ (T ⤳ T);
rule neg [<int>] $i ↪ Int.— $i;

// `(qdiv t1 t2)`: If `t1` and `t2` are values of the same category and `t2`
// is non-zero, then this returns the rational division of `t1` and `t2`.
sequential symbol qdiv [T1 T2]: τ (T1 ⤳ T2 ⤳ <rat>);
rule qdiv [<int>] [<int>] $i $j ↪ qdiv (to_q $i) (to_q $j)
with qdiv [<rat>] [<rat>] $x $y ↪ qdiv $x $y;

// `(zdiv t1 t2)`:
// - If `t1` and `t2` are numeral values and `t2` is non-zero, then this
//   returns the integer division (floor) of `t1` and `t2`.
// - If `t1` and `t2` are bitwise values of the same category and bitwidth,
//   then this returns their (total, unsigned) division, where division by
//   zero returns the max unsigned value.
sequential symbol zdiv [T : Set]: τ (T ⤳ T ⤳ T);
//rule zdiv [<int>] $i $j ↪ Int.zdiv $i $j
//with zdiv [<rat>] $x $y ↪ Int.zdiv (to_z $x) (to_z $y);

// `(zmod t1 t2)`:
// - If `t1` and `t2` are numeral values and `t2` is non-zero, then this
//   returns the integer remainder of `t1` and `t2`.
// - If `t1` and `t2` are bitwise values of the same category and bitwidth,
//   then this returns their (total, unsigned) remainder, where remainder by
//   zero returns `t1`.
sequential symbol zmod [T : Set]: τ (T ⤳ T ⤳ T);
//rule zmod [<int>] $i $j ↪ Int.zmod $i $j;

// `(is_neg t1)`: If `t1` is an arithmetic value, this returns `true` if `t1`
// is strictly negative and `false` otherwise. Otherwise, this operator is not
// evaluated.
sequential symbol is_neg [T : Set]: τ (T ⤳ Bool);
rule is_neg [<int>] $i ↪ Int.isZneg $i;

// `(gt t1 t2)`: Equivalent to `(is_neg (add (neg t1) t2))`.
sequential symbol gt [T1 : Set] [T2 : Set]: τ (T1 ⤳ T2 ⤳ Bool);
rule gt [<int>] [<int>] $i $j ↪ isGt ($i Int.≐ $j);


// ---- bitvectors. ----
// `(len t1)`:
// - Binary length (bitwidth) if `t1` is a binary value.
// - String length if `t1` is a string value.
sequential symbol len [T : Set]: τ (T ⤳ <int>);

// `(concat t1 t2)`:
// - The concatenation of bits if `t1` and `t2` are binary values.
// - The concatenation of strings if `t1` and `t2` are string values.
sequential symbol concat [T : Set]: τ (T ⤳ T ⤳ T);

// `(extract t1 t2 t3)`:
// - If `t1` is a binary value and `t2` and `t3` are numeral values, this
//   returns the binary value corresponding to the bits in `t1` from position
//   `t2` through `t3` if `0<=t2`, or the empty binary value otherwise.
// - If `t1` is a string value and `t2` and `t3` are numeral values, this
//   returns the string value corresponding to the characters in `t1` from
//   position `t2` through `t3` inclusive if `0<=t2`, or the empty string value
//   otherwise.
sequential symbol extract [T : Set]: τ (T ⤳ <int> ⤳ <int> ⤳ T);

// `(find t1 t2)`: If `t1` and `t2` are string values, this returns a
// numeral value corresponding to the first index (left to right) where `t2`
// occurs as a substring of `t1`, or the numeral value `-1` otherwise.
sequential symbol find : τ (<str> ⤳ <str> ⤳ <int>);


// ---- list operators. ----
// `(nil f T)`: If `f` is a right associative operator and `T` is a ground
// type, return its nil terminator. If `f` has a parametric nil terminator,
// return the terminator is specialized for `T`.
sequential symbol nil [T1 T2]
    (f : τ (T1 ⤳ T2 ⤳ T2))
    (T : τ Type) : τ T;

// `(cons f t1 t2)`: If `t2` is an `f`-list, then this returns the term `(f t1 t2)`.
sequential symbol cons [U : Set] [T : Set] :
	τ ((U ⤳ T ⤳ T) ⤳ U ⤳ T ⤳ T);
rule cons $f $x ($f ⋅ $y ⋅ $ys)
  ↪ $f ⋅ $x ⋅ ($f ⋅ $y ⋅ $ys)
with cons [_] [$T] $f $x $xs
  ↪ requires $xs (nil $f $T) ($f ⋅ $x ⋅ $xs);

sequential  symbol fold [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (L.list T1 ⤳ T2);
rule fold $f ($x L.⸬ $xs) ↪ $f ⋅ $x ⋅ (fold $f $xs)
with fold [_] [$T2] $f L.□          ↪ nil $f $T2;

sequential symbol unfold [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ L.list T1);
rule unfold $f ($f ⋅ $x ⋅ $xs) ↪ $x L.⸬ (unfold $f $xs)
with unfold [_] [$T2] $f $z ↪ requires $z (nil $f $T2) L.□;

// `(list_concat f t1 t2)`: If `t1` is an `f`-list with children
// `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`, this
// returns `(f t11 ... t1n t21 ... t2m)` if `n+m>0` and `nil` otherwise.
// Otherwise, this operator does not evaluate.
sequential symbol list_concat
  [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) :
  τ (T2 ⤳ T2 ⤳ T2);
rule list_concat $f $xs $ys ↪ fold $f (unfold $f $xs L.++ unfold $f $ys);



// `(list_len f t)`: If `t` is an `f`-list with children `t1 ... tn`, then
// this returns `n`.
symbol length [a] : L.𝕃 a → Int.ℤ;
rule length L.□ ↪ 0
with length (_ L.⸬ $xs) ↪ 1 Int.+ length $xs;

sequential symbol list_len [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) :
  τ (T2 ⤳ <int>);
rule list_len $f $xs ↪ length (unfold $f $xs);

// `(list_nth f t1 t2)`: If `t1` is `(f s0 ... s{n-1})` and `t2` is a numeral
// value such that `0<=t2<n`, then this returns `s_{t2}`. Otherwise, this
// operator does not evaluate.
sequential symbol nth [a] : L.𝕃 a → Int.ℤ → τ a;
rule nth ($x L.⸬ _) 0 ↪ $x
with nth (_ L.⸬ $xs) $n ↪ nth $xs ($n Int.+ -1);

sequential symbol list_nth [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ <int> ⤳ T1);
rule list_nth $f $xs $i ↪ nth (unfold $f $xs) $i;

// `(list_find f t1 t2)`: If `t1` is `(f s0 ... s{n-1})`, then this returns
// the smallest numeral value `i` such that `t2` is syntactically equal to
// `si`, or `-1` if no such `si` can be found. Otherwise, this operator does
// not evaluate.
symbol index [a] : τ a → L.𝕃 a → Int.ℤ;
rule index $x ($y L.⸬ $xs) ↪
  ite (eq $x $y) 0 (1 Int.+ index $x $xs);

sequential symbol list_mem [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T1 ⤳ Bool);
rule list_mem [$T1] [_] $f $xs $x ↪ L.∈ (eq [$T1] [$T1]) $x (unfold $f $xs);

sequential symbol list_find [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T1 ⤳ <int>);
rule list_find $f $xs $x
  ↪ ite (list_mem $f $xs $x) (index $x (unfold $f $xs)) -1;

// `(list_rev f t1)`: If `t1` is an `f`-list with children `t11 ... t1n`,
// then this returns `(f t1n ... t11)`.
sequential symbol list_rev [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2);
rule list_rev $f $xs ↪ fold $f (L.rev (unfold $f $xs));

// `(list_erase f t1 t2)`:
// If `t1` is an `f`-list, then this returns the
// result of removing the first occurrence of `t2` from `t1` if it exists.
// Returns `t1` unchanged if it does not contain `t2`.
symbol rem [a] : τ a → L.𝕃 a → L.𝕃 a;
rule rem _ L.□ ↪ L.□
with rem $x ($y L.⸬ $ys)
  ↪ ite (eq $x $y) $ys ($y L.⸬ rem $x $ys);

sequential symbol list_erase [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T1 ⤳ T2);
rule list_erase $f $xs $x ↪ fold $f (rem $x (unfold $f $xs));

// `(list_erase_all f t1 t2)`: If `t1` is an `f`-list, then this returns the
// result of removing all occurrences of `t2` from `t1`, where the remaining
// elements are kept in order. Returns `t1` unchanged if it does not
// contain `t2`.
sequential symbol list_erase_all [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T1 ⤳ T2);
rule list_erase_all $f $xs $x
  ↪ let ys ≔ unfold $f $xs in
    let ys' ≔ L.filter (λ y, not (eq $x y)) ys in
    fold $f ys';

// `(list_setof f t1)`: If `t1` is an `f`-list with children `t11 ... t1n`,
// this returns the `f`-list obtained by dropping each element from this list
// beyond the first occurrence. Note that the remaining elements are kept in
// order.

// Helper: undup that keeps FIRST occurrence (stdlib's undup keeps last)
// Eunoia spec says list_setof should keep first occurrence
symbol undup_first [a] : L.𝕃 a → L.𝕃 a;
rule undup_first L.□ ↪ L.□
with undup_first ($x L.⸬ $xs) ↪
  $x L.⸬ undup_first (L.filter (λ y, not (eq $x y)) $xs);

sequential symbol list_setof [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2);
rule list_setof $f $xs
  ↪ let ys ≔ unfold $f $xs in
    fold $f (undup_first ys);

// Helper: count occurrences of an element in a list
symbol count_occ [a] : τ a → L.𝕃 a → Int.ℤ;
rule count_occ _ L.□ ↪ 0
with count_occ $x ($y L.⸬ $ys) ↪ ite (eq $x $y) (1 Int.+ count_occ $x $ys) (count_occ $x $ys);



// Helper: check if for all elements of first list, their count in first list
// is <= their count in second list
symbol minclude_check [a] : L.𝕃 a → L.𝕃 a → L.𝕃 a → 𝔹;
rule minclude_check _ L.□ _ ↪ true
with minclude_check $full ($x L.⸬ $xs) $ys ↪
  and (not (isGt (count_occ $x $full Int.≐ count_occ $x $ys)))
      (minclude_check $full $xs $ys);


// `(list_minclude f t1 t2)`: (Multiset inclusion) If `t1` is an `f`-list
// with children `t11 ... t1n` and `t2` is an `f`-list with children
// `t21 ... t2m`, then this returns true if each unique element in
// `t11 ... t1n` occurs with the greater than or equal multiplicity in
// `t21 ... t2m`. Note that order of the elements does not matter.
sequential symbol list_minclude [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2 ⤳ Bool);
rule list_minclude $f $xs $ys ↪
  let xs' ≔ unfold $f $xs in
  let ys' ≔ unfold $f $ys in
  minclude_check xs' xs' ys';


// `(list_meq f t1 t2)`: (Multiset equal) Equivalent to
// `(and (list_minclude f t1 t2) (list_minclude f t2 t1))`.
sequential symbol list_meq [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2 ⤳ Bool);
rule list_meq $f $xs $ys ↪ and (list_minclude $f $xs $ys) (list_minclude $f $ys $xs);



// `(list_diff f t1 t2)`: (Difference) If `t1` is an `f`-list with children
// `t11 ... t1n` and `t2` is an `f`-list with children `t21 ... t2m`, this
// returns the result of erasing elements of `t11 ... t1n` that occur in
// `t21 ... t2m` where multiplicity is considered. In detail, for each
// `i = 1, ..., n`, if `t1i` occurs in `t21 ... t2m`, we remove one copy of
// it from that list. Otherwise if `t1i` does not occur in `t21 ... t2m`,
// we append it to the final result.
// Helper: diff_aux xs ys returns (result, remaining_ys)
// where result contains elements of xs not in ys (with multiplicity)
symbol diff_aux [a] : L.𝕃 a → L.𝕃 a → L.𝕃 a;
rule diff_aux L.□ _ ↪ L.□
with diff_aux ($x L.⸬ $xs) $ys ↪
  ite (L.∈ eq $x $ys)
      (diff_aux $xs (rem $x $ys))
      ($x L.⸬ diff_aux $xs $ys);

sequential symbol list_diff [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2 ⤳ T2);
rule list_diff $f $xs $ys ↪
  fold $f (diff_aux (unfold $f $xs) (unfold $f $ys));
// `(list_inter f t1 t2)`: (Intersection) If `t1` is an `f`-list with
// children `t11 ... t1n` and `t2` is an `f`-list with children
// `t21 ... t2m`, this returns the result of erasing elements of `t11 ... t1n`
// that do not occur in `t21 ... t2m` where multiplicity is considered. In
// detail, for each `i = 1, ..., n`, if `t1i` occurs in `t21 ... t2m`, we
// erase one copy of it from that list and append it to the final result.
// Helper: inter_aux xs ys returns elements of xs that are also in ys (with multiplicity)
symbol inter_aux [a] : L.𝕃 a → L.𝕃 a → L.𝕃 a;
rule inter_aux L.□ _ ↪ L.□
with inter_aux ($x L.⸬ $xs) $ys ↪
  ite (L.∈ eq $x $ys)
      ($x L.⸬ inter_aux $xs (rem $x $ys))
      (inter_aux $xs $ys);

sequential symbol list_inter [T1 T2] (f : τ (T1 ⤳ T2 ⤳ T2)) : τ (T2 ⤳ T2 ⤳ T2);
rule list_inter $f $xs $ys ↪
  fold $f (inter_aux (unfold $f $xs) (unfold $f $ys));
// `(list_singleton_elim f t1)`: (Singleton elimination) If `t1` is an
// `f`-list containing a single child `t11`, this returns `t11`. All other
// `f`-lists `t1` are returned unchanged. Otherwise, this operator does not
// evaluate.
// Note: In Eunoia, this can return T1 when singleton but T2 otherwise.
// For our encoding, we restrict to the common case where T1 = T2.
sequential symbol list_singleton_elim [T] (f : τ (T ⤳ T ⤳ T)) : τ (T ⤳ T);
// Helper to check if unfolded list is a singleton and return element or original
sequential symbol singleton_elim_aux [T] : τ (T ⤳ T ⤳ T) → L.𝕃 T → τ T → τ T;
// If the list has exactly one element, return that element
// Otherwise return the original term
rule singleton_elim_aux _ ($x L.⸬ L.□) _ ↪ $x
with singleton_elim_aux _ _ $orig ↪ $orig;

rule list_singleton_elim $f $xs ↪ singleton_elim_aux $f (unfold $f $xs) $xs;

// eo::List, eo::List::cons, eo::List::nil
symbol List : τ Type;
sequential symbol List__nil : τ List; symbol ∎ ≔ List__nil;
sequential symbol List__cons [T : Set]: τ (T ⤳ List ⤳ List);

// nil rule for List__cons
rule nil List__cons List ↪ List__nil;
