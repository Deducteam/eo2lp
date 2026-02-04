require open cpc.theories.Arith;
require open cpc.theories.Arrays;

// ============================================================
// Type declarations
// ============================================================

// Array is a binary type constructor
assert ⊢ Array : τ ({|eo::Type|} ⤳ ({|eo::Type|} ⤳ {|eo::Type|}));

// select and store with Int -> Int arrays
assert ⊢ select : τ (Array Int Int ⤳ (Int ⤳ Int));
assert ⊢ store : τ (Array Int Int ⤳ (Int ⤳ (Int ⤳ Array Int Int)));

// select and store with Bool -> Int arrays
assert ⊢ select : τ (Array Bool Int ⤳ (Bool ⤳ Int));
assert ⊢ store : τ (Array Bool Int ⤳ (Bool ⤳ (Int ⤳ Array Bool Int)));

// select and store with Int -> Bool arrays
assert ⊢ select : τ (Array Int Bool ⤳ (Int ⤳ Bool));
assert ⊢ store : τ (Array Int Bool ⤳ (Int ⤳ (Bool ⤳ Array Int Bool)));

// ============================================================
// Array type is a proper Set
// ============================================================

assert ⊢ Array Int Int : Set;
assert ⊢ Array Bool Int : Set;
assert ⊢ Array Int Bool : Set;
assert ⊢ Array Bool Bool : Set;

// ============================================================
// Nested array types
// ============================================================

// Array of arrays
assert ⊢ Array Int (Array Int Int) : Set;
assert ⊢ select : τ (Array Int (Array Int Int) ⤳ (Int ⤳ Array Int Int));
assert ⊢ store : τ (Array Int (Array Int Int) ⤳ (Int ⤳ ((Array Int Int) ⤳ Array Int (Array Int Int))));

// ============================================================
// Equality on arrays (from Builtin)
// ============================================================

assert ⊢ = : τ (Array Int Int ⤳ (Array Int Int ⤳ Bool));
assert ⊢ = : τ (Array Bool Int ⤳ (Array Bool Int ⤳ Bool));

// ============================================================
// Arith symbols accessible in Arrays context
// ============================================================

assert ⊢ Int : Set;
assert ⊢ {|eo::add|} (of_Z 1) (of_Z 2) ≡ of_Z 3;
assert ⊢ {|eo::mul|} (of_Z 3) (of_Z 4) ≡ of_Z 12;

// ============================================================
// eo::eq on types
// ============================================================

assert ⊢ {|eo::eq|} Int Int ≡ true;
assert ⊢ {|eo::eq|} Int Bool ≡ false;

// ============================================================
// eo::typeof -- type of array-typed expressions
// (cannot test directly without array values, but can test
//  that integer operations still work in context)
// ============================================================

assert ⊢ {|eo::typeof|} (of_Z 0) ≡ Int;
assert ⊢ {|eo::typeof|} true ≡ Bool;

// ============================================================
// Boolean operations in Arrays context
// ============================================================

assert ⊢ {|eo::and|} true true ≡ true;
assert ⊢ {|eo::or|} false true ≡ true;
assert ⊢ {|eo::not|} false ≡ true;

// ============================================================
// eo::ite with array-compatible types
// ============================================================

assert ⊢ {|eo::ite|} true (of_Z 1) (of_Z 2) ≡ of_Z 1;
assert ⊢ {|eo::ite|} false (of_Z 1) (of_Z 2) ≡ of_Z 2;

// ============================================================
// eo::eq / eo::is_z for integers in Arrays context
// ============================================================

assert ⊢ {|eo::eq|} (of_Z 5) (of_Z 5) ≡ true;
assert ⊢ {|eo::eq|} (of_Z 5) (of_Z 6) ≡ false;
assert ⊢ {|eo::is_z|} (of_Z 0) ≡ true;
