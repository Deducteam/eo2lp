require open cpc.programs.Quantifiers;

// ============================================================
// $contains_atomic_term -- subterm search
// "The result is true if arg2 is a subterm of arg1."
// Base case: (eo::eq x y)
// Recursive case: search in function and argument of application
// ============================================================

// Atomic equality: same term → true
assert ⊢ {|$contains_atomic_term|} true true ≡ true;
assert ⊢ {|$contains_atomic_term|} false false ≡ true;
assert ⊢ {|$contains_atomic_term|} (of_Z 1) (of_Z 1) ≡ true;
assert ⊢ {|$contains_atomic_term|} (of_Z 0) (of_Z 0) ≡ true;

// Atomic inequality: different terms → false
assert ⊢ {|$contains_atomic_term|} true false ≡ false;
assert ⊢ {|$contains_atomic_term|} (of_Z 1) (of_Z 2) ≡ false;
assert ⊢ {|$contains_atomic_term|} (of_Z 0) (of_Z 1) ≡ false;

// Application: (not true) contains true → true
assert ⊢ {|$contains_atomic_term|} (APP not true) true ≡ true;

// Application: (not true) contains false → false (not is not false)
assert ⊢ {|$contains_atomic_term|} (APP not true) false ≡ false;

// Application: (not true) contains not → true (not is the function head)
assert ⊢ {|$contains_atomic_term|} (APP not true) not ≡ true;

// Nested: (and true false) contains true → true
assert ⊢ {|$contains_atomic_term|} (APP (APP and true) false) true ≡ true;

// Nested: (and true false) contains false → true
assert ⊢ {|$contains_atomic_term|} (APP (APP and true) false) false ≡ true;

// Nested: (and true false) contains and → true
assert ⊢ {|$contains_atomic_term|} (APP (APP and true) false) and ≡ true;

// Nested: (and true true) does not contain false → false
assert ⊢ {|$contains_atomic_term|} (APP (APP and true) true) false ≡ false;

// Deep: (not (and true false)) contains false → true
assert ⊢ {|$contains_atomic_term|} (APP not (APP (APP and true) false)) false ≡ true;

// Integer terms: (+ 1 2) contains 1 → true
assert ⊢ {|$contains_atomic_term|} (APP (APP (+) (of_Z 1)) (of_Z 2)) (of_Z 1) ≡ true;

// Integer terms: (+ 1 2) contains 3 → false
assert ⊢ {|$contains_atomic_term|} (APP (APP (+) (of_Z 1)) (of_Z 2)) (of_Z 3) ≡ false;

// ============================================================
// $contains_atomic_term_list -- subterm search against a list
// "True if any atomic (0-ary) subterm of t is in xs."
// Base: check if x is in xs via eo::list_find
// ============================================================

// Atomic term in list → true
assert ⊢ {|$contains_atomic_term_list|} true
  (APP (APP ({|eo::List::cons|}) true) {|eo::List::nil|})
  ≡ true;

// Atomic term not in list → false
assert ⊢ {|$contains_atomic_term_list|} false
  (APP (APP ({|eo::List::cons|}) true) {|eo::List::nil|})
  ≡ false;

// Application: (not true) with [true] → true (true is a subterm)
assert ⊢ {|$contains_atomic_term_list|} (APP not true)
  (APP (APP ({|eo::List::cons|}) true) {|eo::List::nil|})
  ≡ true;

// Application: (not true) with [false] → false
assert ⊢ {|$contains_atomic_term_list|} (APP not true)
  (APP (APP ({|eo::List::cons|}) false) {|eo::List::nil|})
  ≡ false;

// Integer term in list
assert ⊢ {|$contains_atomic_term_list|} (of_Z 5)
  (APP (APP ({|eo::List::cons|}) (of_Z 5)) {|eo::List::nil|})
  ≡ true;

// Integer term not in list
assert ⊢ {|$contains_atomic_term_list|} (of_Z 5)
  (APP (APP ({|eo::List::cons|}) (of_Z 6)) {|eo::List::nil|})
  ≡ false;

// Multiple elements in list: (of_Z 1) in [2, 1] → true
assert ⊢ {|$contains_atomic_term_list|} (of_Z 1)
  (APP (APP ({|eo::List::cons|}) (of_Z 2))
    (APP (APP ({|eo::List::cons|}) (of_Z 1)) {|eo::List::nil|}))
  ≡ true;

// ============================================================
// $substitute -- term substitution
// "The result of replacing all occurrences of arg1 with arg2 in arg3."
// Rules:
//   (substitute x y x) → y
//   (substitute x y z) → z  (z ≠ x)
//   (substitute x y (f a)) → APP (substitute x y f) (substitute x y a)
// ============================================================

// Base case: substitute x for y in x → y
assert ⊢ {|$substitute|} true false true ≡ false;
assert ⊢ {|$substitute|} false true false ≡ true;

// Base case: substitute x for y in z (z ≠ x) → z
assert ⊢ {|$substitute|} true false false ≡ false;
assert ⊢ {|$substitute|} false true true ≡ true;

// Integer substitution
assert ⊢ {|$substitute|} (of_Z 1) (of_Z 99) (of_Z 1) ≡ of_Z 99;
assert ⊢ {|$substitute|} (of_Z 1) (of_Z 99) (of_Z 2) ≡ of_Z 2;
assert ⊢ {|$substitute|} (of_Z 1) (of_Z 99) (of_Z 0) ≡ of_Z 0;

// Application: substitute in (not true), replacing true with false
// → APP (substitute true false not) (substitute true false true)
// → APP not false
assert ⊢ {|$substitute|} true false (APP not true) ≡ APP not false;

// Application: substitute in (not false), replacing true with false
// → APP not false (no change since true not present)
assert ⊢ {|$substitute|} true false (APP not false) ≡ APP not false;

// Nested: substitute in (and true true), replacing true with false
// → APP (APP and false) false
assert ⊢ {|$substitute|} true false (APP (APP and true) true) ≡ APP (APP and false) false;

// Nested: substitute in (and true false), replacing true with false
// → APP (APP and false) false
assert ⊢ {|$substitute|} true false (APP (APP and true) false) ≡ APP (APP and false) false;

// Variable substitution
assert ⊢ {|$substitute|}
  ({|eo::var|} "x" Int) (of_Z 42)
  ({|eo::var|} "x" Int)
  ≡ of_Z 42;

// Variable not matched
assert ⊢ {|$substitute|}
  ({|eo::var|} "x" Int) (of_Z 42)
  ({|eo::var|} "y" Int)
  ≡ {|eo::var|} "y" Int;

// Variable in application
assert ⊢ {|$substitute|}
  ({|eo::var|} "x" Int) (of_Z 42)
  (APP (APP (+) ({|eo::var|} "x" Int)) (of_Z 1))
  ≡ APP (APP (+) (of_Z 42)) (of_Z 1);

// ============================================================
// $contains_atomic_term_list_free -- free variable search
// "True if any atomic (0-ary) subterm of t is in xs and is not
//  a bound variable of t at that position."
// ============================================================

// Atomic term in list, no bound vars → true
assert ⊢ {|$contains_atomic_term_list_free|} true
  (APP (APP ({|eo::List::cons|}) true) {|eo::List::nil|})
  ≡ true;

// Atomic term not in list → false
assert ⊢ {|$contains_atomic_term_list_free|} false
  (APP (APP ({|eo::List::cons|}) true) {|eo::List::nil|})
  ≡ false;

// ============================================================
// Type declarations accessible
// ============================================================

assert ⊢ forall : τ ({|eo::List|} ⤳ (Bool ⤳ Bool));
assert ⊢ exists : τ ({|eo::List|} ⤳ (Bool ⤳ Bool));

// ============================================================
// Arithmetic/Boolean operations accessible
// ============================================================

assert ⊢ {|eo::add|} (of_Z 1) (of_Z 2) ≡ of_Z 3;
assert ⊢ {|eo::eq|} true true ≡ true;
assert ⊢ {|eo::not|} true ≡ false;
assert ⊢ {|eo::and|} true true ≡ true;
assert ⊢ {|eo::or|} false true ≡ true;
