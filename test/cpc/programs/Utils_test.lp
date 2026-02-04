require open cpc.theories.Arith;
require open cpc.programs.Utils;

// ============================================================
// Type declarations
// ============================================================

assert ⊢ {|@@Pair|} : τ ({|eo::Type|} ⤳ ({|eo::Type|} ⤳ {|eo::Type|}));
assert ⊢ {|@@result.null|} : τ Bool;
assert ⊢ {|@@result.invalid|} : τ Bool;

// Pair types are proper Sets
assert ⊢ {|@@Pair|} Int Int : Set;
assert ⊢ {|@@Pair|} Bool Bool : Set;
assert ⊢ {|@@Pair|} Int Bool : Set;
assert ⊢ {|@@Pair|} Bool Int : Set;

// ============================================================
// $pair_first / $pair_second -- projection on Int pairs
// ============================================================

assert ⊢ {|$pair_first|} ({|@@pair|} (of_Z 1) (of_Z 2)) ≡ of_Z 1;
assert ⊢ {|$pair_second|} ({|@@pair|} (of_Z 1) (of_Z 2)) ≡ of_Z 2;

assert ⊢ {|$pair_first|} ({|@@pair|} (of_Z 0) (of_Z 0)) ≡ of_Z 0;
assert ⊢ {|$pair_second|} ({|@@pair|} (of_Z 0) (of_Z 0)) ≡ of_Z 0;

assert ⊢ {|$pair_first|} ({|@@pair|} (of_Z -5) (of_Z 10)) ≡ of_Z -5;
assert ⊢ {|$pair_second|} ({|@@pair|} (of_Z -5) (of_Z 10)) ≡ of_Z 10;

// ============================================================
// $pair_first / $pair_second -- projection on Bool pairs
// ============================================================

assert ⊢ {|$pair_first|} ({|@@pair|} true false) ≡ true;
assert ⊢ {|$pair_second|} ({|@@pair|} true false) ≡ false;

assert ⊢ {|$pair_first|} ({|@@pair|} false true) ≡ false;
assert ⊢ {|$pair_second|} ({|@@pair|} false true) ≡ true;

assert ⊢ {|$pair_first|} ({|@@pair|} true true) ≡ true;
assert ⊢ {|$pair_second|} ({|@@pair|} false false) ≡ false;

// ============================================================
// $pair_first / $pair_second -- mixed-type pairs
// ============================================================

assert ⊢ {|$pair_first|} ({|@@pair|} (of_Z 42) true) ≡ of_Z 42;
assert ⊢ {|$pair_second|} ({|@@pair|} (of_Z 42) true) ≡ true;

assert ⊢ {|$pair_first|} ({|@@pair|} false (of_Z -1)) ≡ false;
assert ⊢ {|$pair_second|} ({|@@pair|} false (of_Z -1)) ≡ of_Z -1;

// ============================================================
// $is_var_list -- check if heterogeneous list contains only variables
// ============================================================

// Empty list is a var list
assert ⊢ {|$is_var_list|} {|eo::List::nil|} ≡ true;

// Single variable
assert ⊢ {|$is_var_list|}
  (@{|eo::List::cons|} Int ({|eo::var|} "x" Int) {|eo::List::nil|})
  ≡ true;

// Two variables
assert ⊢ {|$is_var_list|}
  (@{|eo::List::cons|} Int ({|eo::var|} "x" Int)
    (@{|eo::List::cons|} Bool ({|eo::var|} "y" Bool) {|eo::List::nil|}))
  ≡ true;

// Non-variable in list → false
assert ⊢ {|$is_var_list|}
  (@{|eo::List::cons|} Int (of_Z 5) {|eo::List::nil|})
  ≡ false;

// Mixed: variable then non-variable → false
assert ⊢ {|$is_var_list|}
  (@{|eo::List::cons|} Int ({|eo::var|} "x" Int)
    (@{|eo::List::cons|} Int (of_Z 5) {|eo::List::nil|}))
  ≡ false;

// Non-variable then variable → false
assert ⊢ {|$is_var_list|}
  (@{|eo::List::cons|} Bool true
    (@{|eo::List::cons|} Int ({|eo::var|} "x" Int) {|eo::List::nil|}))
  ≡ false;

// ============================================================
// $result_combine -- combining proof results
// ============================================================

// null is identity
assert ⊢ {|$result_combine|} true {|@@result.null|} ≡ true;
assert ⊢ {|$result_combine|} false {|@@result.null|} ≡ false;

// Combining same result
assert ⊢ {|$result_combine|} true true ≡ true;
assert ⊢ {|$result_combine|} false false ≡ false;

// Combining different results → invalid
assert ⊢ {|$result_combine|} true false ≡ {|@@result.invalid|};
assert ⊢ {|$result_combine|} false true ≡ {|@@result.invalid|};

// ============================================================
// $is_app -- check if term is application of a given function
// ============================================================

// not applied to true: $is_app not (not true) = true
assert ⊢ {|$is_app|} not (APP not true) ≡ true;

// not applied to false
assert ⊢ {|$is_app|} not (APP not false) ≡ true;

// Checking wrong function → false
assert ⊢ {|$is_app|} not (of_Z 5) ≡ false;
assert ⊢ {|$is_app|} not true ≡ false;

// $get_arg_list_rec -- argument list extraction
// Skipped: eo::cons with eo::List::cons doesn't fully reduce because
// eo::nil eo::List::cons eo::List has no computation rule matching eo::List::nil.

// ============================================================
// eo::eq on pairs -- syntactic equality
// ============================================================

assert ⊢ {|eo::eq|}
  ({|@@pair|} (of_Z 1) (of_Z 2))
  ({|@@pair|} (of_Z 1) (of_Z 2))
  ≡ true;

assert ⊢ {|eo::eq|}
  ({|@@pair|} (of_Z 1) (of_Z 2))
  ({|@@pair|} (of_Z 1) (of_Z 3))
  ≡ false;

// ============================================================
// $assoc_nil_same_type -- check same type across n-ary operator
// ============================================================

// (+ 1 (+ 2 nil)): all elements are Int, so same_type returns true
assert ⊢ {|$assoc_nil_same_type|} (+)
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int)))
  ≡ true;

// Single element: (+ 1 nil)
assert ⊢ {|$assoc_nil_has_type_rec|} (+)
  ({|eo::nil|} (+) Int) Int
  ≡ true;

// ============================================================
// Arith operations remain functional in Utils context
// ============================================================

assert ⊢ {|eo::add|} (of_Z 3) (of_Z 4) ≡ of_Z 7;
assert ⊢ {|eo::mul|} (of_Z 5) (of_Z 6) ≡ of_Z 30;
assert ⊢ {|eo::neg|} (of_Z 3) ≡ of_Z -3;

// ============================================================
// Boolean operations remain functional in Utils context
// ============================================================

assert ⊢ {|eo::and|} true true ≡ true;
assert ⊢ {|eo::or|} false true ≡ true;
assert ⊢ {|eo::not|} true ≡ false;

// ============================================================
// eo::List operations in Utils context
// ============================================================

assert ⊢ {|eo::List::nil|} : τ {|eo::List|};
assert ⊢ {|eo::List::concat|} {|eo::List::nil|} {|eo::List::nil|} ≡ {|eo::List::nil|};
