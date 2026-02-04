require open cpc.programs.DistinctValues;

// ============================================================
// $are_distinct_terms -- two terms are semantically distinct
// "True if we can show that t and s are semantically distinct,
//  e.g. (not (= t s)) holds."
// ============================================================

// Same integer → false (not distinct)
assert ⊢ {|$are_distinct_terms|} (of_Z 1) (of_Z 1) ≡ false;
assert ⊢ {|$are_distinct_terms|} (of_Z 0) (of_Z 0) ≡ false;
assert ⊢ {|$are_distinct_terms|} (of_Z -5) (of_Z -5) ≡ false;

// Different integers → true (distinct)
assert ⊢ {|$are_distinct_terms|} (of_Z 1) (of_Z 2) ≡ true;
assert ⊢ {|$are_distinct_terms|} (of_Z 0) (of_Z -1) ≡ true;
assert ⊢ {|$are_distinct_terms|} (of_Z 3) (of_Z -3) ≡ true;
assert ⊢ {|$are_distinct_terms|} (of_Z 100) (of_Z 200) ≡ true;

// Same boolean → false
assert ⊢ {|$are_distinct_terms|} true true ≡ false;
assert ⊢ {|$are_distinct_terms|} false false ≡ false;

// Different booleans → true
assert ⊢ {|$are_distinct_terms|} true false ≡ true;
assert ⊢ {|$are_distinct_terms|} false true ≡ true;

// ============================================================
// $are_distinct_terms_type -- type-specific distinctness check
// "True if we can show that t and s are semantically distinct."
// First rule: same term → false
// Int rule: both must be integer values (eo::is_z)
// Bool rule: both must be boolean values (eo::is_bool)
// ============================================================

// Same term → false (first rule fires)
assert ⊢ {|$are_distinct_terms_type|} (of_Z 5) (of_Z 5) Int ≡ false;
assert ⊢ {|$are_distinct_terms_type|} true true Bool ≡ false;

// Different integers → and(is_z(ti), is_z(si)) = and(true, true) = true
assert ⊢ {|$are_distinct_terms_type|} (of_Z 1) (of_Z 2) Int ≡ true;
assert ⊢ {|$are_distinct_terms_type|} (of_Z 0) (of_Z -1) Int ≡ true;

// Different booleans → and(is_bool(tb), is_bool(sb)) = true
assert ⊢ {|$are_distinct_terms_type|} true false Bool ≡ true;
assert ⊢ {|$are_distinct_terms_type|} false true Bool ≡ true;

// ============================================================
// $are_distinct_terms_list_rec -- one term vs list of terms
// "True if t can be shown to be disequal from all terms in xs."
// ============================================================

// t=1 vs empty list → true (vacuously distinct from all)
assert ⊢ {|$are_distinct_terms_list_rec|} (of_Z 1)
  {|eo::List::nil|} Int
  ≡ true;

// t=1 vs [2] → are_distinct_terms_type(1,2,Int) = true → recurse on empty → true
assert ⊢ {|$are_distinct_terms_list_rec|} (of_Z 1)
  (@{|eo::List::cons|} Int (of_Z 2) {|eo::List::nil|})
  Int
  ≡ true;

// t=1 vs [1] → are_distinct_terms_type(1,1,Int) = false → false
assert ⊢ {|$are_distinct_terms_list_rec|} (of_Z 1)
  (@{|eo::List::cons|} Int (of_Z 1) {|eo::List::nil|})
  Int
  ≡ false;

// t=1 vs [2, 3] → both distinct → true
assert ⊢ {|$are_distinct_terms_list_rec|} (of_Z 1)
  (@{|eo::List::cons|} Int (of_Z 2)
    (@{|eo::List::cons|} Int (of_Z 3) {|eo::List::nil|}))
  Int
  ≡ true;

// t=1 vs [2, 1] → 1 distinct from 2 but not from 1 → false
assert ⊢ {|$are_distinct_terms_list_rec|} (of_Z 1)
  (@{|eo::List::cons|} Int (of_Z 2)
    (@{|eo::List::cons|} Int (of_Z 1) {|eo::List::nil|}))
  Int
  ≡ false;

// ============================================================
// $are_distinct_terms_list -- pairwise distinctness of a list
// "True if each pair of terms in xs can be shown to be pairwise disequal."
// ============================================================

// Empty list → true
assert ⊢ {|$are_distinct_terms_list|}
  {|eo::List::nil|} Int
  ≡ true;

// Singleton [1] → true (no pairs to check)
assert ⊢ {|$are_distinct_terms_list|}
  (@{|eo::List::cons|} Int (of_Z 1) {|eo::List::nil|})
  Int
  ≡ true;

// [1, 2] → 1 distinct from 2 → true
assert ⊢ {|$are_distinct_terms_list|}
  (@{|eo::List::cons|} Int (of_Z 1)
    (@{|eo::List::cons|} Int (of_Z 2) {|eo::List::nil|}))
  Int
  ≡ true;

// [1, 1] → 1 not distinct from 1 → false
assert ⊢ {|$are_distinct_terms_list|}
  (@{|eo::List::cons|} Int (of_Z 1)
    (@{|eo::List::cons|} Int (of_Z 1) {|eo::List::nil|}))
  Int
  ≡ false;

// [1, 2, 3] → all pairwise distinct → true
assert ⊢ {|$are_distinct_terms_list|}
  (@{|eo::List::cons|} Int (of_Z 1)
    (@{|eo::List::cons|} Int (of_Z 2)
      (@{|eo::List::cons|} Int (of_Z 3) {|eo::List::nil|})))
  Int
  ≡ true;

// [1, 2, 1] → 1 appears twice → false
assert ⊢ {|$are_distinct_terms_list|}
  (@{|eo::List::cons|} Int (of_Z 1)
    (@{|eo::List::cons|} Int (of_Z 2)
      (@{|eo::List::cons|} Int (of_Z 1) {|eo::List::nil|})))
  Int
  ≡ false;

// Booleans: [true, false] → distinct → true
assert ⊢ {|$are_distinct_terms_list|}
  (@{|eo::List::cons|} Bool true
    (@{|eo::List::cons|} Bool false {|eo::List::nil|}))
  Bool
  ≡ true;

// Booleans: [true, true] → not distinct → false
assert ⊢ {|$are_distinct_terms_list|}
  (@{|eo::List::cons|} Bool true
    (@{|eo::List::cons|} Bool true {|eo::List::nil|}))
  Bool
  ≡ false;

// ============================================================
// $some_pairwise_distinct_term -- pointwise check of two lists
// "True if there is some term in ts and ss at the same position
//  which can be shown to be semantically distinct."
// ============================================================

// Both empty → false
assert ⊢ {|$some_pairwise_distinct_term|} {|eo::List::nil|} {|eo::List::nil|} ≡ false;

// [1] vs [2] → are_distinct_terms(1,2) = true → true
assert ⊢ {|$some_pairwise_distinct_term|}
  (@{|eo::List::cons|} Int (of_Z 1) {|eo::List::nil|})
  (@{|eo::List::cons|} Int (of_Z 2) {|eo::List::nil|})
  ≡ true;

// [1] vs [1] → not distinct → recurse → false
assert ⊢ {|$some_pairwise_distinct_term|}
  (@{|eo::List::cons|} Int (of_Z 1) {|eo::List::nil|})
  (@{|eo::List::cons|} Int (of_Z 1) {|eo::List::nil|})
  ≡ false;

// [1, 2] vs [1, 3] → first pair not distinct, second pair distinct → true
assert ⊢ {|$some_pairwise_distinct_term|}
  (@{|eo::List::cons|} Int (of_Z 1)
    (@{|eo::List::cons|} Int (of_Z 2) {|eo::List::nil|}))
  (@{|eo::List::cons|} Int (of_Z 1)
    (@{|eo::List::cons|} Int (of_Z 3) {|eo::List::nil|}))
  ≡ true;

// [1, 2] vs [1, 2] → no position is distinct → false
assert ⊢ {|$some_pairwise_distinct_term|}
  (@{|eo::List::cons|} Int (of_Z 1)
    (@{|eo::List::cons|} Int (of_Z 2) {|eo::List::nil|}))
  (@{|eo::List::cons|} Int (of_Z 1)
    (@{|eo::List::cons|} Int (of_Z 2) {|eo::List::nil|}))
  ≡ false;

// ============================================================
// $set_is_not_subset -- set non-subset check
// "True if we can show that t is not a subset of s based on
//  reasoning about values."
// ============================================================

// empty ⊄ anything → false (empty is always a subset)
assert ⊢ {|$set_is_not_subset|}
  (@{|set.empty|} Int)
  (@{|set.singleton|} Int (of_Z 1))
  ≡ false;

// {1} ⊄ empty → true (1 is not in empty)
assert ⊢ {|$set_is_not_subset|}
  (@{|set.singleton|} Int (of_Z 1))
  (@{|set.empty|} Int)
  ≡ true;

// {1} ⊄ {1} → are_distinct_terms(1,1) = false → false
assert ⊢ {|$set_is_not_subset|}
  (@{|set.singleton|} Int (of_Z 1))
  (@{|set.singleton|} Int (of_Z 1))
  ≡ false;

// {1} ⊄ {2} → are_distinct_terms(1,2) = true → true
assert ⊢ {|$set_is_not_subset|}
  (@{|set.singleton|} Int (of_Z 1))
  (@{|set.singleton|} Int (of_Z 2))
  ≡ true;

// ============================================================
// Arithmetic/boolean builtins accessible in DistinctValues context
// ============================================================

assert ⊢ {|eo::add|} (of_Z 1) (of_Z 2) ≡ of_Z 3;
assert ⊢ {|eo::eq|} (of_Z 1) (of_Z 1) ≡ true;
assert ⊢ {|eo::is_z|} (of_Z 5) ≡ true;
assert ⊢ {|eo::is_bool|} true ≡ true;
