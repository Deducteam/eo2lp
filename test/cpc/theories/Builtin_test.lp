require open cpc.theories.Builtin;

// ============================================================
// Type declarations
// ============================================================

// Boolean connectives have correct types
assert ⊢ not : τ (Bool ⤳ Bool);
assert ⊢ or : τ (Bool ⤳ (Bool ⤳ Bool));
assert ⊢ and : τ (Bool ⤳ (Bool ⤳ Bool));
assert ⊢ => : τ (Bool ⤳ (Bool ⤳ Bool));
assert ⊢ xor : τ (Bool ⤳ (Bool ⤳ Bool));

// Polymorphic symbols -- instantiated at Bool
assert ⊢ ite : τ (Bool ⤳ (Bool ⤳ (Bool ⤳ Bool)));
assert ⊢ = : τ (Bool ⤳ (Bool ⤳ Bool));
assert ⊢ distinct : τ ({|eo::List|} ⤳ Bool);

// ============================================================
// Nil rules for n-ary operators
// ============================================================

assert ⊢ {|eo::nil|} or Bool ≡ false;
assert ⊢ {|eo::nil|} and Bool ≡ true;

// ============================================================
// eo::not -- truth table
// ============================================================

assert ⊢ {|eo::not|} true ≡ false;
assert ⊢ {|eo::not|} false ≡ true;

// ============================================================
// eo::and -- truth table
// ============================================================

assert ⊢ {|eo::and|} true true ≡ true;
assert ⊢ {|eo::and|} true false ≡ false;
assert ⊢ {|eo::and|} false true ≡ false;
assert ⊢ {|eo::and|} false false ≡ false;

// ============================================================
// eo::or -- truth table
// ============================================================

assert ⊢ {|eo::or|} true true ≡ true;
assert ⊢ {|eo::or|} true false ≡ true;
assert ⊢ {|eo::or|} false true ≡ true;
assert ⊢ {|eo::or|} false false ≡ false;

// ============================================================
// eo::xor -- truth table
// ============================================================

assert ⊢ {|eo::xor|} true true ≡ false;
assert ⊢ {|eo::xor|} true false ≡ true;
assert ⊢ {|eo::xor|} false true ≡ true;
assert ⊢ {|eo::xor|} false false ≡ false;

// ============================================================
// eo::ite -- conditional on booleans
// ============================================================

assert ⊢ {|eo::ite|} true true false ≡ true;
assert ⊢ {|eo::ite|} false true false ≡ false;
assert ⊢ {|eo::ite|} true false true ≡ false;
assert ⊢ {|eo::ite|} false false true ≡ true;

// ============================================================
// eo::eq -- syntactic equality on booleans
// ============================================================

assert ⊢ {|eo::eq|} true true ≡ true;
assert ⊢ {|eo::eq|} false false ≡ true;
assert ⊢ {|eo::eq|} true false ≡ false;
assert ⊢ {|eo::eq|} false true ≡ false;

// ============================================================
// eo::is_bool -- boolean value test
// ============================================================

assert ⊢ {|eo::is_bool|} true ≡ true;
assert ⊢ {|eo::is_bool|} false ≡ true;

// ============================================================
// eo::requires -- guarded evaluation
// ============================================================

assert ⊢ {|eo::requires|} true true false ≡ false;
assert ⊢ {|eo::requires|} false false true ≡ true;

// ============================================================
// eo::typeof -- type extraction
// ============================================================

assert ⊢ {|eo::typeof|} true ≡ Bool;
assert ⊢ {|eo::typeof|} false ≡ Bool;

// ============================================================
// eo::as -- identity cast
// ============================================================

assert ⊢ {|eo::as|} Bool true ≡ true;
assert ⊢ {|eo::as|} Bool false ≡ false;

// ============================================================
// eo::var / eo::is_var -- variable binding
// ============================================================

assert ⊢ {|eo::is_var|} ({|eo::var|} "x" Bool) ≡ true;
assert ⊢ {|eo::is_var|} true ≡ false;
assert ⊢ {|eo::is_var|} false ≡ false;

// ============================================================
// eo::nameof -- name extraction from variables
// ============================================================

assert ⊢ {|eo::nameof|} ({|eo::var|} "x" Bool) ≡ "x";
assert ⊢ {|eo::nameof|} ({|eo::var|} "abc" Bool) ≡ "abc";

// ============================================================
// ?? -- type-level conditional
// ============================================================

assert ⊢ τ (?? true Bool Bool) ≡ τ Bool;
assert ⊢ τ (?? false Bool Bool) ≡ τ Bool;

// ============================================================
// Compound expressions
// ============================================================

// not(and(true, false)) = not(false) = true
assert ⊢ {|eo::not|} ({|eo::and|} true false) ≡ true;

// or(and(true, true), false) = or(true, false) = true
assert ⊢ {|eo::or|} ({|eo::and|} true true) false ≡ true;

// xor(not(true), false) = xor(false, false) = false
assert ⊢ {|eo::xor|} ({|eo::not|} true) false ≡ false;

// and(or(true, false), or(false, true)) = and(true, true) = true
assert ⊢ {|eo::and|} ({|eo::or|} true false) ({|eo::or|} false true) ≡ true;

// ite(and(true,true), not(false), xor(true,true))
//   = ite(true, true, false) = true
assert ⊢ {|eo::ite|} ({|eo::and|} true true) ({|eo::not|} false) ({|eo::xor|} true true) ≡ true;

// eq(not(true), false) = eq(false, false) = true
assert ⊢ {|eo::eq|} ({|eo::not|} true) false ≡ true;

// eo::List -- heterogeneous list basics
assert ⊢ {|eo::List::nil|} : τ {|eo::List|};
assert ⊢ {|eo::List::concat|} {|eo::List::nil|} {|eo::List::nil|} ≡ {|eo::List::nil|};
