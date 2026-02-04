require open cpc.theories.Ints;

// ============================================================
// Type declarations
// ============================================================

assert ⊢ div : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ mod : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ divisible : τ (Int ⤳ (Int ⤳ Bool));
assert ⊢ div_total : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ mod_total : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ abs : τ (Int ⤳ Int);

// Power/log symbols
assert ⊢ {|int.pow2|} : τ (Int ⤳ Int);
assert ⊢ {|int.log2|} : τ (Int ⤳ Int);
assert ⊢ {|int.ispow2|} : τ (Int ⤳ Bool);

// Error marker symbols
assert ⊢ {|@int_div_by_zero|} : τ (Int ⤳ Int);
assert ⊢ {|@mod_by_zero|} : τ (Int ⤳ Int);

// ============================================================
// Ints re-exports Arith symbols
// ============================================================

assert ⊢ Int : Set;
assert ⊢ of_Z : τ (int ⤳ Int);
assert ⊢ + : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ * : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ < : τ (Int ⤳ (Int ⤳ Bool));
assert ⊢ <= : τ (Int ⤳ (Int ⤳ Bool));
assert ⊢ > : τ (Int ⤳ (Int ⤳ Bool));
assert ⊢ >= : τ (Int ⤳ (Int ⤳ Bool));

// ============================================================
// Arithmetic builtins remain functional in Ints context
// ============================================================

assert ⊢ {|eo::add|} (of_Z 10) (of_Z 5) ≡ of_Z 15;
assert ⊢ {|eo::add|} (of_Z -3) (of_Z -7) ≡ of_Z -10;
assert ⊢ {|eo::mul|} (of_Z 3) (of_Z 7) ≡ of_Z 21;
assert ⊢ {|eo::mul|} (of_Z 0) (of_Z 100) ≡ of_Z 0;
assert ⊢ {|eo::neg|} (of_Z 4) ≡ of_Z -4;
assert ⊢ {|eo::neg|} (of_Z -9) ≡ of_Z 9;

// ============================================================
// eo::zdiv / eo::zmod -- declared without computation rules
// ============================================================

assert ⊢ {|eo::zdiv|} : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ {|eo::zmod|} : τ (Int ⤳ (Int ⤳ Int));

// ============================================================
// Comparison builtins in Ints context
// ============================================================

assert ⊢ {|eo::eq|} (of_Z 5) (of_Z 5) ≡ true;
assert ⊢ {|eo::eq|} (of_Z 5) (of_Z 6) ≡ false;
assert ⊢ {|eo::gt|} (of_Z 10) (of_Z 3) ≡ true;
assert ⊢ {|eo::gt|} (of_Z 3) (of_Z 10) ≡ false;
assert ⊢ {|eo::gt|} (of_Z 0) (of_Z 0) ≡ false;
assert ⊢ {|eo::is_neg|} (of_Z -1) ≡ true;
assert ⊢ {|eo::is_neg|} (of_Z 0) ≡ false;
assert ⊢ {|eo::is_neg|} (of_Z 1) ≡ false;

// ============================================================
// Nested arithmetic in Ints context
// ============================================================

// add(mul(2,3), neg(4)) = 6 + (-4) = 2
assert ⊢ {|eo::add|} ({|eo::mul|} (of_Z 2) (of_Z 3)) ({|eo::neg|} (of_Z 4)) ≡ of_Z 2;

// is_neg(add(-10, 5)) = is_neg(-5) = true
assert ⊢ {|eo::is_neg|} ({|eo::add|} (of_Z -10) (of_Z 5)) ≡ true;

// gt(mul(3,3), mul(2,4)) = gt(9,8) = true
assert ⊢ {|eo::gt|} ({|eo::mul|} (of_Z 3) (of_Z 3)) ({|eo::mul|} (of_Z 2) (of_Z 4)) ≡ true;

// ============================================================
// eo::ite in Ints context
// ============================================================

assert ⊢ {|eo::ite|} true (of_Z 1) (of_Z 2) ≡ of_Z 1;
assert ⊢ {|eo::ite|} false (of_Z 1) (of_Z 2) ≡ of_Z 2;

// ============================================================
// Nil rules accessible in Ints context
// ============================================================

assert ⊢ {|eo::nil|} (+) Int ≡ of_Z 0;
assert ⊢ {|eo::nil|} (*) Int ≡ of_Z 1;

// ============================================================
// eo::is_z in Ints context
// ============================================================

assert ⊢ {|eo::is_z|} (of_Z 0) ≡ true;
assert ⊢ {|eo::is_z|} (of_Z -99) ≡ true;

// ============================================================
// eo::to_z in Ints context
// ============================================================

assert ⊢ {|eo::to_z|} (of_Z 7) ≡ of_Z 7;
assert ⊢ {|eo::to_z|} (of_Z -3) ≡ of_Z -3;
