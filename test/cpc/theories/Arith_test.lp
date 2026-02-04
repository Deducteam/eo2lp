require open cpc.theories.Arith;

// ============================================================
// Type declarations
// ============================================================

assert ⊢ Int : Set;
assert ⊢ of_Z : τ (int ⤳ Int);
assert ⊢ + : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ * : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ - : τ (Int ⤳ Int);
assert ⊢ -_1 : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ < : τ (Int ⤳ (Int ⤳ Bool));
assert ⊢ <= : τ (Int ⤳ (Int ⤳ Bool));
assert ⊢ > : τ (Int ⤳ (Int ⤳ Bool));
assert ⊢ >= : τ (Int ⤳ (Int ⤳ Bool));
assert ⊢ abs : τ (Int ⤳ Int);

// ============================================================
// eo::add -- integer addition
// ============================================================

assert ⊢ {|eo::add|} (of_Z 2) (of_Z 3) ≡ of_Z 5;
assert ⊢ {|eo::add|} (of_Z -1) (of_Z 1) ≡ of_Z 0;
assert ⊢ {|eo::add|} (of_Z 0) (of_Z 0) ≡ of_Z 0;
assert ⊢ {|eo::add|} (of_Z 100) (of_Z -50) ≡ of_Z 50;
assert ⊢ {|eo::add|} (of_Z -10) (of_Z -20) ≡ of_Z -30;
assert ⊢ {|eo::add|} (of_Z 0) (of_Z 7) ≡ of_Z 7;
assert ⊢ {|eo::add|} (of_Z 7) (of_Z 0) ≡ of_Z 7;

// ============================================================
// eo::mul -- integer multiplication
// ============================================================

assert ⊢ {|eo::mul|} (of_Z 4) (of_Z 5) ≡ of_Z 20;
assert ⊢ {|eo::mul|} (of_Z -2) (of_Z 3) ≡ of_Z -6;
assert ⊢ {|eo::mul|} (of_Z 0) (of_Z 99) ≡ of_Z 0;
assert ⊢ {|eo::mul|} (of_Z 99) (of_Z 0) ≡ of_Z 0;
assert ⊢ {|eo::mul|} (of_Z 1) (of_Z 42) ≡ of_Z 42;
assert ⊢ {|eo::mul|} (of_Z -3) (of_Z -4) ≡ of_Z 12;
assert ⊢ {|eo::mul|} (of_Z 7) (of_Z 1) ≡ of_Z 7;

// ============================================================
// eo::neg -- integer negation
// ============================================================

assert ⊢ {|eo::neg|} (of_Z 7) ≡ of_Z -7;
assert ⊢ {|eo::neg|} (of_Z -3) ≡ of_Z 3;
assert ⊢ {|eo::neg|} (of_Z 0) ≡ of_Z 0;
assert ⊢ {|eo::neg|} (of_Z 1) ≡ of_Z -1;

// Double negation
assert ⊢ {|eo::neg|} ({|eo::neg|} (of_Z 5)) ≡ of_Z 5;

// ============================================================
// eo::is_neg -- negative test
// ============================================================

assert ⊢ {|eo::is_neg|} (of_Z -3) ≡ true;
assert ⊢ {|eo::is_neg|} (of_Z -1) ≡ true;
assert ⊢ {|eo::is_neg|} (of_Z 0) ≡ false;
assert ⊢ {|eo::is_neg|} (of_Z 1) ≡ false;
assert ⊢ {|eo::is_neg|} (of_Z 100) ≡ false;

// ============================================================
// eo::gt -- integer greater-than
// ============================================================

assert ⊢ {|eo::gt|} (of_Z 5) (of_Z 3) ≡ true;
assert ⊢ {|eo::gt|} (of_Z 3) (of_Z 3) ≡ false;
assert ⊢ {|eo::gt|} (of_Z 3) (of_Z 5) ≡ false;
assert ⊢ {|eo::gt|} (of_Z 0) (of_Z -1) ≡ true;
assert ⊢ {|eo::gt|} (of_Z -1) (of_Z 0) ≡ false;
assert ⊢ {|eo::gt|} (of_Z -2) (of_Z -5) ≡ true;
assert ⊢ {|eo::gt|} (of_Z -5) (of_Z -2) ≡ false;

// ============================================================
// eo::is_z -- polymorphic integer test
// ============================================================

assert ⊢ {|eo::is_z|} (of_Z 5) ≡ true;
assert ⊢ {|eo::is_z|} (of_Z 0) ≡ true;
assert ⊢ {|eo::is_z|} (of_Z -1) ≡ true;

// ============================================================
// eo::to_z -- identity on integers
// ============================================================

assert ⊢ {|eo::to_z|} (of_Z 42) ≡ of_Z 42;
assert ⊢ {|eo::to_z|} (of_Z 0) ≡ of_Z 0;
assert ⊢ {|eo::to_z|} (of_Z -7) ≡ of_Z -7;

// ============================================================
// eo::zdiv / eo::zmod -- declared but no computation rules
// (just verify they are well-typed)
// ============================================================

assert ⊢ {|eo::zdiv|} : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ {|eo::zmod|} : τ (Int ⤳ (Int ⤳ Int));

// ============================================================
// Combined arithmetic: nested expressions
// ============================================================

// (2 + 3) * 4 = 20
assert ⊢ {|eo::mul|} ({|eo::add|} (of_Z 2) (of_Z 3)) (of_Z 4) ≡ of_Z 20;

// -(2 + 3) = -5
assert ⊢ {|eo::neg|} ({|eo::add|} (of_Z 2) (of_Z 3)) ≡ of_Z -5;

// is_neg(neg(5)) = true
assert ⊢ {|eo::is_neg|} ({|eo::neg|} (of_Z 5)) ≡ true;

// is_neg(add(-1, 2)) = false
assert ⊢ {|eo::is_neg|} ({|eo::add|} (of_Z -1) (of_Z 2)) ≡ false;

// gt(add(2,3), mul(1,4)) = gt(5,4) = true
assert ⊢ {|eo::gt|} ({|eo::add|} (of_Z 2) (of_Z 3)) ({|eo::mul|} (of_Z 1) (of_Z 4)) ≡ true;

// add(mul(2,3), mul(4,5)) = add(6,20) = 26
assert ⊢ {|eo::add|} ({|eo::mul|} (of_Z 2) (of_Z 3)) ({|eo::mul|} (of_Z 4) (of_Z 5)) ≡ of_Z 26;

// neg(mul(-3, -4)) = neg(12) = -12
assert ⊢ {|eo::neg|} ({|eo::mul|} (of_Z -3) (of_Z -4)) ≡ of_Z -12;

// ============================================================
// Nil rules for n-ary operators
// ============================================================

assert ⊢ {|eo::nil|} (+) Int ≡ of_Z 0;
assert ⊢ {|eo::nil|} (*) Int ≡ of_Z 1;

// ============================================================
// eo::list_len -- list length via + operator
// ============================================================

// Empty list has length 0
assert ⊢ {|eo::list_len|} (+) ({|eo::nil|} (+) Int) ≡ of_Z 0;

// Singleton: (+ 1 nil) has length 1
assert ⊢ {|eo::list_len|} (+) (APP (APP (+) (of_Z 1)) ({|eo::nil|} (+) Int)) ≡ of_Z 1;

// Two elements: (+ 1 (+ 2 nil)) has length 2
assert ⊢ {|eo::list_len|} (+)
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int)))
  ≡ of_Z 2;

// Three elements
assert ⊢ {|eo::list_len|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) (APP (APP (+) (of_Z 30)) ({|eo::nil|} (+) Int))))
  ≡ of_Z 3;

// ============================================================
// eo::list_nth -- indexed access
// ============================================================

// First element of (+ 10 (+ 20 (+ 30 nil)))
assert ⊢ {|eo::list_nth|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) (APP (APP (+) (of_Z 30)) ({|eo::nil|} (+) Int))))
  (of_Z 0)
  ≡ of_Z 10;

// Second element
assert ⊢ {|eo::list_nth|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) (APP (APP (+) (of_Z 30)) ({|eo::nil|} (+) Int))))
  (of_Z 1)
  ≡ of_Z 20;

// Third element
assert ⊢ {|eo::list_nth|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) (APP (APP (+) (of_Z 30)) ({|eo::nil|} (+) Int))))
  (of_Z 2)
  ≡ of_Z 30;

// ============================================================
// eo::list_find -- find element index
// ============================================================

// Find 10 in (+ 10 (+ 20 (+ 30 nil))) = 0
assert ⊢ {|eo::list_find|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) (APP (APP (+) (of_Z 30)) ({|eo::nil|} (+) Int))))
  (of_Z 10)
  ≡ of_Z 0;

// Find 20 = 1
assert ⊢ {|eo::list_find|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) (APP (APP (+) (of_Z 30)) ({|eo::nil|} (+) Int))))
  (of_Z 20)
  ≡ of_Z 1;

// Find 30 = 2
assert ⊢ {|eo::list_find|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) (APP (APP (+) (of_Z 30)) ({|eo::nil|} (+) Int))))
  (of_Z 30)
  ≡ of_Z 2;

// Find missing element = -1
assert ⊢ {|eo::list_find|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) ({|eo::nil|} (+) Int)))
  (of_Z 99)
  ≡ of_Z -1;

// ============================================================
// eo::list_concat -- list concatenation
// ============================================================

// Concat empty with empty
assert ⊢ {|eo::list_concat|} (+) ({|eo::nil|} (+) Int) ({|eo::nil|} (+) Int)
  ≡ {|eo::nil|} (+) Int;

// Concat singleton with empty
assert ⊢ {|eo::list_concat|} (+)
  (APP (APP (+) (of_Z 1)) ({|eo::nil|} (+) Int))
  ({|eo::nil|} (+) Int)
  ≡ APP (APP (+) (of_Z 1)) ({|eo::nil|} (+) Int);

// ============================================================
// eo::list_mem -- list membership
// ============================================================

// Member found
assert ⊢ {|eo::list_mem|} (+)
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int)))
  (of_Z 1)
  ≡ true;

assert ⊢ {|eo::list_mem|} (+)
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int)))
  (of_Z 2)
  ≡ true;

// Member not found
assert ⊢ {|eo::list_mem|} (+)
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int)))
  (of_Z 3)
  ≡ false;

// Empty list membership
assert ⊢ {|eo::list_mem|} (+)
  ({|eo::nil|} (+) Int)
  (of_Z 1)
  ≡ false;

// ============================================================
// eo::eq on integers
// ============================================================

assert ⊢ {|eo::eq|} (of_Z 0) (of_Z 0) ≡ true;
assert ⊢ {|eo::eq|} (of_Z 1) (of_Z 2) ≡ false;
assert ⊢ {|eo::eq|} (of_Z -1) (of_Z -1) ≡ true;

// ============================================================
// eo::ite on integers
// ============================================================

assert ⊢ {|eo::ite|} true (of_Z 10) (of_Z 20) ≡ of_Z 10;
assert ⊢ {|eo::ite|} false (of_Z 10) (of_Z 20) ≡ of_Z 20;
assert ⊢ {|eo::ite|} ({|eo::gt|} (of_Z 5) (of_Z 3)) (of_Z 1) (of_Z 0) ≡ of_Z 1;
assert ⊢ {|eo::ite|} ({|eo::gt|} (of_Z 3) (of_Z 5)) (of_Z 1) (of_Z 0) ≡ of_Z 0;

// ============================================================
// eo::typeof on integers
// ============================================================

assert ⊢ {|eo::typeof|} (of_Z 3) ≡ Int;
assert ⊢ {|eo::typeof|} (of_Z 0) ≡ Int;

// ============================================================
// eo::is_var on integers
// ============================================================

assert ⊢ {|eo::is_var|} (of_Z 5) ≡ false;
assert ⊢ {|eo::is_var|} ({|eo::var|} "x" Int) ≡ true;
assert ⊢ {|eo::nameof|} ({|eo::var|} "y" Int) ≡ "y";
