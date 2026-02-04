require open cpc.theories.Arith;
require open cpc.rules.Arrays;

// Declare test arrays and indices
symbol a : τ (Array Int Int);
symbol b : τ (Array Int Int);
symbol i : τ Int;
symbol j : τ Int;
symbol e : τ Int;
symbol f : τ Int;

// ============================================================
// arrays_read_over_write_1: read after write at same index
// ============================================================

// select(store(a, i, e), i) = e
assert ⊢ arrays_read_over_write_1 (select (store a i e) i)
         : Proof (APP (APP = (select (store a i e) i)) e);

// ============================================================
// arrays_read_over_write: read after write at different index
// ============================================================

// Given not(i = j), select(store(a, i, e), j) = select(a, j)
assert ⊢ arrays_read_over_write (select (store a i e) j)
         : Proof (APP not (APP (APP = i) j))
           → Proof (APP (APP = (select (store a i e) j)) (select a j));

// ============================================================
// arrays_read_over_write_contra: contradiction from unequal reads
// ============================================================

// If select(store(a,i,e),j) ≠ select(a,j) then j = i
assert ⊢ arrays_read_over_write_contra
         : Proof (APP not (APP (APP (@= Int) (select (store a i e) j)) (select a j)))
           → Proof (APP (APP = j) i);

// ============================================================
// arrays_ext: extensionality
// ============================================================

// If a ≠ b, then there exists an index where they differ
assert ⊢ arrays_ext
         : Proof (APP not (APP (APP (@= (Array Int Int)) a) b))
           → Proof (APP not (APP (APP = (select a ({|@array_deq_diff|} a b)))
                                       (select b ({|@array_deq_diff|} a b))));
