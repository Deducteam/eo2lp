// ============================================================================
// Prelude_tests.lp - Test cases for Eunoia builtin operators
// ============================================================================
//
// This file contains test cases for the Eunoia computational operators,
// taken directly from the Ethos User Manual (eo-user-manual.md).
//
// These tests verify that the Lambdapi encoding of Eunoia builtins
// behaves correctly according to the specification.
//
// Note: Many tests are commented out because they require features not yet
// fully implemented (bitvectors, strings, rationals, etc.) or because they
// test non-evaluation behavior which is harder to express in Lambdapi.
// ============================================================================

require open
  Stdlib.Set
  Stdlib.HOL
  Stdlib.List
  Stdlib.String
  Stdlib.Z
  Stdlib.Bool
  prelude.Prelude;

// ============================================================================
// Boolean Operator Tests
// ============================================================================
// From: Computation Examples section of eo-user-manual.md

// --- eo::and ---
// (eo::and true false) == false
assert ⊢ and true false ≡ false;

// (eo::and true true) == true
assert ⊢ and true true ≡ true;

// (eo::and false true) == false
assert ⊢ and false true ≡ false;

// (eo::and false false) == false
assert ⊢ and false false ≡ false;

// (eo::and #b1110 #b0110) == #b0110
// Note: Bitvector operations not yet implemented

// --- eo::or ---
// (eo::or true false) == true
assert ⊢ or true false ≡ true;

// (eo::or true true) == true
assert ⊢ or true true ≡ true;

// (eo::or false true) == true
assert ⊢ or false true ≡ true;

// (eo::or false false) == false
assert ⊢ or false false ≡ false;

// --- eo::not ---
// (eo::not true) == false
assert ⊢ not true ≡ false;

// (eo::not false) == true
assert ⊢ not false ≡ true;

// (eo::not #b1010) == #b0101
// Note: Bitvector operations not yet implemented

// --- eo::xor ---
// (eo::xor true true) == false
assert ⊢ xor true true ≡ false;

// (eo::xor true false) == true
assert ⊢ xor true false ≡ true;

// (eo::xor false true) == true
assert ⊢ xor false true ≡ true;

// (eo::xor false false) == false
assert ⊢ xor false false ≡ false;

// (eo::xor #b111 #b011) == #b100
// Note: Bitvector operations not yet implemented

// ============================================================================
// Arithmetic Operator Tests
// ============================================================================
// From: Computation Examples section of eo-user-manual.md

// Note: Integer and rational arithmetic requires Stdlib.Z and ℚ operations
// which may need additional rewrite rules to be fully functional.

// (eo::add 1 1) == 2
// (eo::add 1 1 1 0) == 3
// (eo::add 1/2 1/3) == 5/6
// (eo::add 2 1/3) == (eo::add 2 1/3)  ; no mixed arithmetic
// (eo::add 2/1 1/3) == 7/3
// (eo::add #b01 #b01) == #b10

// (eo::mul 2 7) == 14
// (eo::mul 2 2 7) == 28
// (eo::mul 1/2 1/4) == 1/8

// (eo::neg -15) == 15

// (eo::qdiv 12 6) == 3/1
// (eo::qdiv 7 2) == 7/2
// (eo::qdiv 7/1 2/1) == 7/2
// (eo::qdiv 7 0) == (eo::qdiv 7 0)  ; no division by zero

// (eo::zdiv 12 3) == 4
// (eo::zdiv 7 2) == 3

// (eo::is_neg 0) == false
// (eo::is_neg -7/2) == true

// ============================================================================
// String Operator Tests
// ============================================================================
// From: Computation Examples section of eo-user-manual.md

// (eo::len "abc") == 3
// (eo::len """hi""") == 4
// (eo::len "\u{AB0E}") == 1
// (eo::len "\uA") == 3

// (eo::concat "abc" "def") == "abcdef"

// (eo::extract "abcdef" 0 1) == "ab"
// (eo::extract "abcdef" -1 3) == ""
// (eo::extract "abcdef" 1 10) == "bcdef"

// (eo::find "abc" "bc") == 1
// (eo::find "abc" "") == 0
// (eo::find "abcdef" "g") == -1

// ============================================================================
// Bitvector Operator Tests
// ============================================================================
// From: Computation Examples section of eo-user-manual.md

// (eo::len #b11100) == 5

// (eo::concat #b000 #b11) == #b00011

// (eo::extract #b11100 2 4) == #b111
// (eo::extract #b11100 2 1) == #b
// (eo::extract #b111000 1 10) == #b11100
// (eo::extract #b10 -1 2) == #b

// ============================================================================
// Conversion Operator Tests
// ============================================================================
// From: Computation Examples section of eo-user-manual.md

// (eo::to_z 3/2) == 1
// (eo::to_z 45) == 45
// (eo::to_z "A") == 65
// (eo::to_z "1") == 49
// (eo::to_z "451") == (eo::to_z "451")  ; string is not length one
// (eo::to_z "") == (eo::to_z "")  ; string is not length one
// (eo::to_z "\u{9876}") == 9876

// (eo::to_q 6) == 6/1

// (eo::to_bin 4 3) == #b0011
// (eo::to_bin 4 #b1) == #b0001
// (eo::to_bin 2 #b10101010) == #b10

// (eo::to_str 65) == "A"
// (eo::to_str 123) == "{"
// (eo::to_str -1) == (eo::to_str -1)  ; since not a valid code point
// (eo::to_str 200000) == (eo::to_str 200000)  ; since not a valid code point
// (eo::to_str 1/2) == "1/2"
// (eo::to_str #b101) == "#b101"

// ============================================================================
// Core Operator Tests
// ============================================================================
// From: Core Computation Examples section of eo-user-manual.md
//
// Setup from manual:
// (declare-const Int Type)
// (declare-const x Int)
// (declare-const y Int)
// (declare-const a Bool)

symbol x : τ <int>;
symbol y : τ <int>;
symbol a : τ Bool;

// --- eo::ite ---
// (eo::ite false x y) == y
assert ⊢ ite false x y ≡ y;

// (eo::ite true Bool Int) == Bool
// Note: This tests type-level ite, which works differently in Lambdapi

// (eo::ite a x x) == (eo::ite a x x)  ; a is not a value
// Note: Non-evaluation is implicit when a is not true/false

// --- eo::eq ---
// (eo::eq x x) == true
assert ⊢ eq x x ≡ true;

// (eo::eq 0 1) == false
// Note: Requires numeral literals

// (eo::eq x y) == false
// Note: In Lambdapi, this would not reduce since x and y are different symbols
// The rule `eq _ _ ↪ false` should apply, but only as a fallback

// (eo::eq 2 (eo::add 1 1)) == true
// Note: Requires arithmetic evaluation

// --- eo::is_eq ---
// (eo::is_eq x x) == true
// (eo::is_eq 0 1) == false
// (eo::is_eq x y) == false
// (eo::is_eq (eo::neg "a") x) == false  ; failed evaluation returns false
// (eo::is_eq 2 (eo::add 1 1)) == true

// --- eo::requires ---
// (eo::requires x 0 true) == (eo::requires x 0 true)  ; x and 0 are not syntactically equal
// (eo::requires x x y) == y
assert ⊢ requires x x y ≡ y;

// (eo::requires x x Int) == Int
// Note: Tests type-level requires

// --- eo::typeof ---
// (eo::typeof x) == <int>  (where x : <int>)
assert ⊢ typeof x ≡ <int>;
assert ⊢ typeof y ≡ <int>;

// --- eo::quote ---
// (eo::quote x) == x
// Note: quote is not yet implemented in Prelude.lp
// assert ⊢ quote x ≡ x;
// assert ⊢ quote true ≡ true;

// ============================================================================
// List Operator Tests
// ============================================================================
// From: List Computation Examples section of eo-user-manual.md
//
// Setup from manual:
// (declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
// (declare-const and (-> Bool Bool Bool) :right-assoc-nil true)
// (declare-const a Bool)
// (declare-const b Bool)
// (declare-const c Bool)
// (declare-const d Bool)
//
// Note: In the manual, `or` and `and` are declared as right-associative
// with nil terminators. The examples show terms in "pre-desugaring" form.
// For example, `(or a b)` actually means `(or a (or b false))` after desugaring.
//
// In our Lambdapi encoding, we need to work with the desugared forms directly.

// We need right-associative operators with nil terminators for list tests.
// In Eunoia: (declare-const or (-> Bool Bool Bool) :right-assoc-nil false)
// In Eunoia: (declare-const and (-> Bool Bool Bool) :right-assoc-nil true)
//
// Lists are written in desugared form:
// - (or a) desugars to (or a false)
// - (or a b) desugars to (or a (or b false))
// - (or a b c) desugars to (or a (or b (or c false)))

symbol lor : τ (Bool ⤳ Bool ⤳ Bool);  // list-or operator
symbol land : τ (Bool ⤳ Bool ⤳ Bool); // list-and operator

// Define nil rules for lor and land so that list operations work
rule nil lor Bool ↪ false;
rule nil land Bool ↪ true;

// ============================================================================
// List Operator Tests (using lor operator with explicit desugared forms)
// ============================================================================

// --- eo::nil ---
// (eo::nil or Bool) == false
assert ⊢ nil lor Bool ≡ false;
assert ⊢ nil land Bool ≡ true;

// --- eo::cons ---
// (eo::cons or a (or a b)) == (or a a b)
assert (a : τ Bool) (b : τ Bool) ⊢
  cons lor a (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))
  ≡ lor ⋅ a ⋅ (lor ⋅ a ⋅ (lor ⋅ b ⋅ false));

// (eo::cons or a false) == (or a)  -- cons onto nil
assert (a : τ Bool) ⊢ cons lor a false ≡ lor ⋅ a ⋅ false;

// --- eo::list_len ---
// (eo::list_len or (or a b)) == 2
assert (a : τ Bool) (b : τ Bool) ⊢ list_len lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ false)) ≡ 2;

// (eo::list_len or (or a b c)) == 3
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_len lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) ≡ 3;

// (eo::list_len or false) == 0
assert ⊢ list_len lor false ≡ 0;

// (eo::list_len or (or a)) == 1
assert (a : τ Bool) ⊢ list_len lor (lor ⋅ a ⋅ false) ≡ 1;

// --- eo::list_concat ---
// (eo::list_concat or false false) == false
assert ⊢ list_concat lor false false ≡ false;

// (eo::list_concat or (or a b) (or c)) == (or a b c)
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_concat lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ false)) (lor ⋅ c ⋅ false)
  ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false));

// (eo::list_concat or false (or b)) == (or b)
assert (b : τ Bool) ⊢ list_concat lor false (lor ⋅ b ⋅ false) ≡ lor ⋅ b ⋅ false;

// (eo::list_concat or (or a b) false) == (or a b)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_concat lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ false)) false ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ false);

// --- eo::list_nth ---
// (eo::list_nth or (or a b c) 0) == a
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_nth lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) 0 ≡ a;

// (eo::list_nth or (or a b c) 1) == b
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_nth lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) 1 ≡ b;

// (eo::list_nth or (or a b c) 2) == c
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_nth lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) 2 ≡ c;

// (eo::list_nth or (or a) 0) == a
assert (a : τ Bool) ⊢ list_nth lor (lor ⋅ a ⋅ false) 0 ≡ a;

// --- eo::list_find ---
// (eo::list_find or (or a b c) a) == 0
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_find lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) a ≡ 0;

// (eo::list_find or (or a b c) b) == 1
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_find lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) b ≡ 1;

// (eo::list_find or (or a b c) c) == 2
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_find lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) c ≡ 2;

// (eo::list_find or (or a b c) d) == -1
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) (d : τ Bool) ⊢
  list_find lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) d ≡ -1;

// --- eo::list_rev ---
// (eo::list_rev or (or a b c)) == (or c b a)
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_rev lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false)))
  ≡ lor ⋅ c ⋅ (lor ⋅ b ⋅ (lor ⋅ a ⋅ false));

// (eo::list_rev or false) == false
assert ⊢ list_rev lor false ≡ false;

// (eo::list_rev or (or a)) == (or a)
assert (a : τ Bool) ⊢ list_rev lor (lor ⋅ a ⋅ false) ≡ lor ⋅ a ⋅ false;

// --- eo::list_erase ---
// (eo::list_erase or (or a b c) a) == (or b c)
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_erase lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) a
  ≡ lor ⋅ b ⋅ (lor ⋅ c ⋅ false);

// (eo::list_erase or (or a b c) b) == (or a c)
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_erase lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) b
  ≡ lor ⋅ a ⋅ (lor ⋅ c ⋅ false);

// (eo::list_erase or (or a b c) d) == (or a b c)  -- element not found
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) (d : τ Bool) ⊢
  list_erase lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) d
  ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false));

// (eo::list_erase or false d) == false
assert (d : τ Bool) ⊢ list_erase lor false d ≡ false;

// Erase first occurrence only: (or a b a) erase a == (or b a)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_erase lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ a ⋅ false))) a
  ≡ lor ⋅ b ⋅ (lor ⋅ a ⋅ false);

// --- eo::list_erase_all ---
// (eo::list_erase_all or (or a b c) a) == (or b c)
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_erase_all lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) a
  ≡ lor ⋅ b ⋅ (lor ⋅ c ⋅ false);

// (eo::list_erase_all or (or a b a) a) == (or b)  -- removes all occurrences
assert (a : τ Bool) (b : τ Bool) ⊢
  list_erase_all lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ a ⋅ false))) a
  ≡ lor ⋅ b ⋅ false;

// (eo::list_erase_all or (or a a a) a) == false  -- all elements removed
assert (a : τ Bool) ⊢
  list_erase_all lor (lor ⋅ a ⋅ (lor ⋅ a ⋅ (lor ⋅ a ⋅ false))) a ≡ false;

// (eo::list_erase_all or (or a b c) d) == (or a b c)
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) (d : τ Bool) ⊢
  list_erase_all lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) d
  ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false));

// --- eo::list_setof ---
// (eo::list_setof or (or a b c)) == (or a b c) -- already unique
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_setof lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false)))
  ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false));

// (eo::list_setof or (or a a a)) == (or a)
assert (a : τ Bool) ⊢
  list_setof lor (lor ⋅ a ⋅ (lor ⋅ a ⋅ (lor ⋅ a ⋅ false))) ≡ lor ⋅ a ⋅ false;

// (eo::list_setof or false) == false
assert ⊢ list_setof lor false ≡ false;

// (eo::list_setof or (or a b a)) == (or a b)  -- first occurrence kept
assert (a : τ Bool) (b : τ Bool) ⊢
  list_setof lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ a ⋅ false)))
  ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ false);

// --- eo::list_minclude ---
// (eo::list_minclude or (or a b) (or a a b)) == true
// {a, b} ⊆ {a, a, b} as multisets: yes
assert (a : τ Bool) (b : τ Bool) ⊢
  list_minclude lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))
                    (lor ⋅ a ⋅ (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))) ≡ true;

// (eo::list_minclude or (or a b) (or b a)) == true
// {a, b} ⊆ {b, a}: yes (same elements)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_minclude lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))
                    (lor ⋅ b ⋅ (lor ⋅ a ⋅ false)) ≡ true;

// (eo::list_minclude or (or a b b) (or a b)) == false
// {a, b, b} ⊆ {a, b}: no (need 2 b's but only have 1)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_minclude lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ b ⋅ false)))
                    (lor ⋅ a ⋅ (lor ⋅ b ⋅ false)) ≡ false;

// (eo::list_minclude or false (or a b)) == true
// {} ⊆ {a, b}: yes (empty set is subset of everything)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_minclude lor false (lor ⋅ a ⋅ (lor ⋅ b ⋅ false)) ≡ true;

// --- eo::list_meq ---
// (eo::list_meq or (or a b) (or a a b)) == false
// {a, b} = {a, a, b}? No (different multiplicities)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_meq lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))
               (lor ⋅ a ⋅ (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))) ≡ false;

// (eo::list_meq or (or a b) (or b a)) == true
// {a, b} = {b, a}? Yes (same multiset)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_meq lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))
               (lor ⋅ b ⋅ (lor ⋅ a ⋅ false)) ≡ true;

// (eo::list_meq or false false) == true
// {} = {}? Yes
assert ⊢ list_meq lor false false ≡ true;

// (eo::list_meq or (or a b c) (or c a b)) == true
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_meq lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false)))
               (lor ⋅ c ⋅ (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))) ≡ true;

// --- eo::list_diff ---
// (eo::list_diff or (or a b) (or a a b)) == false
// {a, b} - {a, a, b} = {} (all elements removed)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_diff lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))
                (lor ⋅ a ⋅ (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))) ≡ false;

// (eo::list_diff or (or a a b) (or a b)) == (or a)
// {a, a, b} - {a, b} = {a} (one a and one b removed)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_diff lor (lor ⋅ a ⋅ (lor ⋅ a ⋅ (lor ⋅ b ⋅ false)))
                (lor ⋅ a ⋅ (lor ⋅ b ⋅ false)) ≡ lor ⋅ a ⋅ false;

// (eo::list_diff or (or a b c) (or c)) == (or a b)
// {a, b, c} - {c} = {a, b}
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_diff lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false)))
                (lor ⋅ c ⋅ false) ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ false);

// (eo::list_diff or (or a b c) false) == (or a b c)
// {a, b, c} - {} = {a, b, c}
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_diff lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))) false
  ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false));

// --- eo::list_inter ---
// (eo::list_inter or (or a b) (or a a b)) == (or a b)
// {a, b} ∩ {a, a, b} = {a, b}
assert (a : τ Bool) (b : τ Bool) ⊢
  list_inter lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))
                 (lor ⋅ a ⋅ (lor ⋅ a ⋅ (lor ⋅ b ⋅ false)))
  ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ false);

// (eo::list_inter or (or a a b) (or a b)) == (or a b)
// {a, a, b} ∩ {a, b} = {a, b} (only one a available in second list)
assert (a : τ Bool) (b : τ Bool) ⊢
  list_inter lor (lor ⋅ a ⋅ (lor ⋅ a ⋅ (lor ⋅ b ⋅ false)))
                 (lor ⋅ a ⋅ (lor ⋅ b ⋅ false))
  ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ false);

// (eo::list_inter or (or a b c) (or d)) == false
// {a, b, c} ∩ {d} = {}
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) (d : τ Bool) ⊢
  list_inter lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false)))
                 (lor ⋅ d ⋅ false) ≡ false;

// (eo::list_inter or (or a b c) (or b c)) == (or b c)
// {a, b, c} ∩ {b, c} = {b, c}
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_inter lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false)))
                 (lor ⋅ b ⋅ (lor ⋅ c ⋅ false))
  ≡ lor ⋅ b ⋅ (lor ⋅ c ⋅ false);

// --- eo::list_singleton_elim ---
// (eo::list_singleton_elim or (or a b c)) == (or a b c)  -- not singleton
assert (a : τ Bool) (b : τ Bool) (c : τ Bool) ⊢
  list_singleton_elim lor (lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false)))
  ≡ lor ⋅ a ⋅ (lor ⋅ b ⋅ (lor ⋅ c ⋅ false));

// (eo::list_singleton_elim or (or a)) == a  -- singleton
assert (a : τ Bool) ⊢ list_singleton_elim lor (lor ⋅ a ⋅ false) ≡ a;

// (eo::list_singleton_elim or false) == false  -- empty list
assert ⊢ list_singleton_elim lor false ≡ false;

// ============================================================================
// eo::List Tests (Heterogeneous List)
// ============================================================================

// The builtin eo::List type with eo::List::cons and eo::List::nil
// is used for datatype introspection (eo::dt_constructors, eo::dt_selectors)

// (eo::nil eo::List::cons eo::List) == eo::List::nil
assert ⊢ nil List__cons List ≡ List__nil;

// ============================================================================
// Additional Edge Case Tests
// ============================================================================

// Double negation for not
assert ⊢ not (not true) ≡ true;
assert ⊢ not (not false) ≡ false;

// Boolean identities
assert ⊢ and true true ≡ true;
assert ⊢ or false false ≡ false;
assert ⊢ xor true false ≡ true;
assert ⊢ xor false true ≡ true;
