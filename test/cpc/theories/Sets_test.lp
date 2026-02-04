require open cpc.theories.Sets;

// ============================================================
// Type declarations -- basic set operations
// ============================================================

// Set type constructor
assert ⊢ {|eo::Set|} : τ ({|eo::Type|} ⤳ {|eo::Type|});

// Set types are proper Sets
assert ⊢ {|eo::Set|} Int : Set;
assert ⊢ {|eo::Set|} Bool : Set;

// ============================================================
// Set operation types with Int
// ============================================================

assert ⊢ {|set.empty|} : τ ({|eo::Set|} Int);
assert ⊢ {|set.singleton|} : τ (Int ⤳ {|eo::Set|} Int);
assert ⊢ {|set.union|} : τ ({|eo::Set|} Int ⤳ ({|eo::Set|} Int ⤳ {|eo::Set|} Int));
assert ⊢ {|set.inter|} : τ ({|eo::Set|} Int ⤳ ({|eo::Set|} Int ⤳ {|eo::Set|} Int));
assert ⊢ {|set.minus|} : τ ({|eo::Set|} Int ⤳ ({|eo::Set|} Int ⤳ {|eo::Set|} Int));
assert ⊢ {|set.member|} : τ (Int ⤳ ({|eo::Set|} Int ⤳ Bool));
assert ⊢ {|set.subset|} : τ ({|eo::Set|} Int ⤳ ({|eo::Set|} Int ⤳ Bool));

// ============================================================
// Set operation types with Bool
// ============================================================

assert ⊢ {|set.empty|} : τ ({|eo::Set|} Bool);
assert ⊢ {|set.singleton|} : τ (Bool ⤳ {|eo::Set|} Bool);
assert ⊢ {|set.union|} : τ ({|eo::Set|} Bool ⤳ ({|eo::Set|} Bool ⤳ {|eo::Set|} Bool));
assert ⊢ {|set.inter|} : τ ({|eo::Set|} Bool ⤳ ({|eo::Set|} Bool ⤳ {|eo::Set|} Bool));
assert ⊢ {|set.minus|} : τ ({|eo::Set|} Bool ⤳ ({|eo::Set|} Bool ⤳ {|eo::Set|} Bool));
assert ⊢ {|set.member|} : τ (Bool ⤳ ({|eo::Set|} Bool ⤳ Bool));
assert ⊢ {|set.subset|} : τ ({|eo::Set|} Bool ⤳ ({|eo::Set|} Bool ⤳ Bool));

// ============================================================
// Additional set operations with Int
// ============================================================

assert ⊢ {|set.choose|} : τ ({|eo::Set|} Int ⤳ Int);
assert ⊢ {|set.is_empty|} : τ ({|eo::Set|} Int ⤳ Bool);
assert ⊢ {|set.is_singleton|} : τ ({|eo::Set|} Int ⤳ Bool);
assert ⊢ {|set.insert|} : τ ({|eo::List|} ⤳ ({|eo::Set|} Int ⤳ {|eo::Set|} Int));

// Additional set operations with Bool
assert ⊢ {|set.choose|} : τ ({|eo::Set|} Bool ⤳ Bool);
assert ⊢ {|set.is_empty|} : τ ({|eo::Set|} Bool ⤳ Bool);
assert ⊢ {|set.is_singleton|} : τ ({|eo::Set|} Bool ⤳ Bool);
assert ⊢ {|set.insert|} : τ ({|eo::List|} ⤳ ({|eo::Set|} Bool ⤳ {|eo::Set|} Bool));

// ============================================================
// Composed set expressions (type checking)
// ============================================================

// union(singleton(1), singleton(2)) is well-typed
assert ⊢ APP (APP {|set.union|}
  (APP {|set.singleton|} (of_Z 1)))
  (APP {|set.singleton|} (of_Z 2))
  : τ ({|eo::Set|} Int);

// member(1, union(s1, s2)) is well-typed
assert ⊢ APP (APP {|set.member|} (of_Z 1))
  (APP (APP {|set.union|}
    (APP {|set.singleton|} (of_Z 1)))
    (APP {|set.singleton|} (of_Z 2)))
  : τ Bool;

// inter(singleton(1), singleton(1)) is well-typed
assert ⊢ APP (APP {|set.inter|}
  (APP {|set.singleton|} (of_Z 1)))
  (APP {|set.singleton|} (of_Z 1))
  : τ ({|eo::Set|} Int);

// minus(singleton(1), empty) is well-typed
assert ⊢ APP (APP {|set.minus|}
  (APP {|set.singleton|} (of_Z 1)))
  {|set.empty|}
  : τ ({|eo::Set|} Int);

// subset(empty, singleton(1)) is well-typed
assert ⊢ APP (APP {|set.subset|}
  {|set.empty|})
  (APP {|set.singleton|} (of_Z 1))
  : τ Bool;

// choose(singleton(1)) is well-typed
assert ⊢ APP {|set.choose|} (APP {|set.singleton|} (of_Z 1)) : τ Int;

// is_empty(empty) is well-typed
assert ⊢ APP {|set.is_empty|} {|set.empty|} : τ Bool;

// is_singleton(singleton(1)) is well-typed
assert ⊢ APP {|set.is_singleton|} (APP {|set.singleton|} (of_Z 1)) : τ Bool;

// ============================================================
// Deeper nesting of set operations
// ============================================================

// union(inter(s1, s2), minus(s1, s2))
assert ⊢ APP (APP {|set.union|}
  (APP (APP {|set.inter|}
    (APP {|set.singleton|} (of_Z 1)))
    (APP {|set.singleton|} (of_Z 2))))
  (APP (APP {|set.minus|}
    (APP {|set.singleton|} (of_Z 1)))
    (APP {|set.singleton|} (of_Z 2)))
  : τ ({|eo::Set|} Int);

// member(choose(s), s) -- well-typed
assert ⊢ APP (APP {|set.member|}
  (APP {|set.choose|} (APP {|set.singleton|} (of_Z 1))))
  (APP {|set.singleton|} (of_Z 1))
  : τ Bool;

// ============================================================
// Equality on sets (from Builtin)
// ============================================================

assert ⊢ = : τ ({|eo::Set|} Int ⤳ ({|eo::Set|} Int ⤳ Bool));
assert ⊢ = : τ ({|eo::Set|} Bool ⤳ ({|eo::Set|} Bool ⤳ Bool));

// ============================================================
// Nested set types
// ============================================================

// Set of sets
assert ⊢ {|eo::Set|} ({|eo::Set|} Int) : Set;
assert ⊢ {|set.empty|} : τ ({|eo::Set|} ({|eo::Set|} Int));
assert ⊢ {|set.singleton|} : τ ({|eo::Set|} Int ⤳ {|eo::Set|} ({|eo::Set|} Int));

// ============================================================
// Arith symbols accessible in Sets context
// ============================================================

assert ⊢ Int : Set;
assert ⊢ {|eo::add|} (of_Z 1) (of_Z 2) ≡ of_Z 3;
assert ⊢ {|eo::mul|} (of_Z 3) (of_Z 4) ≡ of_Z 12;
assert ⊢ {|eo::neg|} (of_Z 5) ≡ of_Z -5;

// ============================================================
// Boolean operations in Sets context
// ============================================================

assert ⊢ {|eo::and|} true true ≡ true;
assert ⊢ {|eo::or|} false true ≡ true;
assert ⊢ {|eo::not|} false ≡ true;
assert ⊢ {|eo::eq|} (of_Z 1) (of_Z 1) ≡ true;
assert ⊢ {|eo::eq|} (of_Z 1) (of_Z 2) ≡ false;
