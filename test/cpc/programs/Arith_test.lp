require open cpc.programs.Arith;

// ============================================================
// $arith_eval_add -- addition wrapper
// ============================================================

assert ⊢ {|$arith_eval_add|} (of_Z 10) (of_Z 20) ≡ of_Z 30;
assert ⊢ {|$arith_eval_add|} (of_Z 0) (of_Z 0) ≡ of_Z 0;
assert ⊢ {|$arith_eval_add|} (of_Z -5) (of_Z 5) ≡ of_Z 0;
assert ⊢ {|$arith_eval_add|} (of_Z -3) (of_Z -7) ≡ of_Z -10;
assert ⊢ {|$arith_eval_add|} (of_Z 100) (of_Z -1) ≡ of_Z 99;

// ============================================================
// $arith_eval_sub -- subtraction wrapper
// ============================================================

assert ⊢ {|$arith_eval_sub|} (of_Z 10) (of_Z 3) ≡ of_Z 7;
assert ⊢ {|$arith_eval_sub|} (of_Z 3) (of_Z 10) ≡ of_Z -7;
assert ⊢ {|$arith_eval_sub|} (of_Z 5) (of_Z 5) ≡ of_Z 0;
assert ⊢ {|$arith_eval_sub|} (of_Z 0) (of_Z 0) ≡ of_Z 0;
assert ⊢ {|$arith_eval_sub|} (of_Z -3) (of_Z -7) ≡ of_Z 4;
assert ⊢ {|$arith_eval_sub|} (of_Z -3) (of_Z 7) ≡ of_Z -10;

// ============================================================
// $arith_eval_mul -- multiplication wrapper
// ============================================================

assert ⊢ {|$arith_eval_mul|} (of_Z 3) (of_Z 4) ≡ of_Z 12;
assert ⊢ {|$arith_eval_mul|} (of_Z 0) (of_Z 99) ≡ of_Z 0;
assert ⊢ {|$arith_eval_mul|} (of_Z -2) (of_Z 5) ≡ of_Z -10;
assert ⊢ {|$arith_eval_mul|} (of_Z -3) (of_Z -4) ≡ of_Z 12;
assert ⊢ {|$arith_eval_mul|} (of_Z 1) (of_Z 42) ≡ of_Z 42;

// ============================================================
// $arith_eval_qsub -- qualified subtraction (same as sub)
// ============================================================

assert ⊢ {|$arith_eval_qsub|} (of_Z 10) (of_Z 3) ≡ of_Z 7;
assert ⊢ {|$arith_eval_qsub|} (of_Z 5) (of_Z 5) ≡ of_Z 0;
assert ⊢ {|$arith_eval_qsub|} (of_Z 0) (of_Z 7) ≡ of_Z -7;

// ============================================================
// $sgn -- sign function
// ============================================================

assert ⊢ {|$sgn|} (of_Z 5) ≡ of_Z 1;
assert ⊢ {|$sgn|} (of_Z 1) ≡ of_Z 1;
assert ⊢ {|$sgn|} (of_Z 100) ≡ of_Z 1;
assert ⊢ {|$sgn|} (of_Z -5) ≡ of_Z -1;
assert ⊢ {|$sgn|} (of_Z -1) ≡ of_Z -1;
assert ⊢ {|$sgn|} (of_Z -100) ≡ of_Z -1;
assert ⊢ {|$sgn|} (of_Z 0) ≡ of_Z 0;

// ============================================================
// $compare_geq -- greater than or equal
// ============================================================

assert ⊢ {|$compare_geq|} (of_Z 5) (of_Z 3) ≡ true;
assert ⊢ {|$compare_geq|} (of_Z 3) (of_Z 5) ≡ false;
assert ⊢ {|$compare_geq|} (of_Z 5) (of_Z 5) ≡ true;
assert ⊢ {|$compare_geq|} (of_Z 0) (of_Z 0) ≡ true;
assert ⊢ {|$compare_geq|} (of_Z -1) (of_Z -2) ≡ true;
assert ⊢ {|$compare_geq|} (of_Z -2) (of_Z -1) ≡ false;
assert ⊢ {|$compare_geq|} (of_Z 0) (of_Z -1) ≡ true;
assert ⊢ {|$compare_geq|} (of_Z -1) (of_Z 0) ≡ false;

// ============================================================
// $arith_eval_int_pow_2_rec -- power of 2 (recursive)
// ============================================================

// 2^0 = 1
assert ⊢ {|$arith_eval_int_pow_2_rec|} (of_Z 0) ≡ of_Z 1;

// 2^1 = 2
assert ⊢ {|$arith_eval_int_pow_2_rec|} (of_Z 1) ≡ of_Z 2;

// 2^2 = 4
assert ⊢ {|$arith_eval_int_pow_2_rec|} (of_Z 2) ≡ of_Z 4;

// 2^3 = 8
assert ⊢ {|$arith_eval_int_pow_2_rec|} (of_Z 3) ≡ of_Z 8;

// ============================================================
// $arith_eval_int_pow_2 -- power of 2 (guarded)
// ============================================================

assert ⊢ {|$arith_eval_int_pow_2|} (of_Z 0) ≡ of_Z 1;
assert ⊢ {|$arith_eval_int_pow_2|} (of_Z 1) ≡ of_Z 2;
assert ⊢ {|$arith_eval_int_pow_2|} (of_Z 3) ≡ of_Z 8;

// Negative exponent → 0
assert ⊢ {|$arith_eval_int_pow_2|} (of_Z -1) ≡ of_Z 0;
assert ⊢ {|$arith_eval_int_pow_2|} (of_Z -5) ≡ of_Z 0;

// $arith_eval_int_log_2_rec -- log base 2 (recursive)
// Skipped: uses eo::zdiv internally which has no computation rules,
// causing non-termination on the catch-all rewrite rule.

// ============================================================
// Nested arithmetic expressions
// ============================================================

// add(mul(2,3), sub(10,4)) = 6 + 6 = 12
assert ⊢ {|$arith_eval_add|}
  ({|$arith_eval_mul|} (of_Z 2) (of_Z 3))
  ({|$arith_eval_sub|} (of_Z 10) (of_Z 4))
  ≡ of_Z 12;

// sgn(sub(3, 5)) = sgn(-2) = -1
assert ⊢ {|$sgn|} ({|$arith_eval_sub|} (of_Z 3) (of_Z 5)) ≡ of_Z -1;

// sgn(add(1, 2)) = sgn(3) = 1
assert ⊢ {|$sgn|} ({|$arith_eval_add|} (of_Z 1) (of_Z 2)) ≡ of_Z 1;

// compare_geq(add(2,3), mul(1,4)) = geq(5,4) = true
assert ⊢ {|$compare_geq|}
  ({|$arith_eval_add|} (of_Z 2) (of_Z 3))
  ({|$arith_eval_mul|} (of_Z 1) (of_Z 4))
  ≡ true;

// compare_geq(mul(2,3), add(5,5)) = geq(6,10) = false
assert ⊢ {|$compare_geq|}
  ({|$arith_eval_mul|} (of_Z 2) (of_Z 3))
  ({|$arith_eval_add|} (of_Z 5) (of_Z 5))
  ≡ false;

// ============================================================
// Type declarations accessible
// ============================================================

assert ⊢ Int : Set;
assert ⊢ div : τ (Int ⤳ (Int ⤳ Int));
assert ⊢ mod : τ (Int ⤳ (Int ⤳ Int));
