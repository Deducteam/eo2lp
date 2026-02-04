require open cpc.theories.Quantifiers;

// ============================================================
// Type declarations
// ============================================================

assert ⊢ forall : τ ({|eo::List|} ⤳ (Bool ⤳ Bool));
assert ⊢ exists : τ ({|eo::List|} ⤳ (Bool ⤳ Bool));

// ============================================================
// $get_var_list type
// ============================================================

assert ⊢ {|$get_var_list|} : τ (Bool ⤳ {|eo::List|});

// ============================================================
// $get_var_list -- extract variable list from quantified formula
// ============================================================

// forall with a concrete variable list: $get_var_list extracts it
// forall [x:Int] true → extract [x:Int]
assert ⊢ {|$get_var_list|}
  (APP (APP forall
    (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int)) {|eo::List::nil|}))
    true)
  ≡ APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int)) {|eo::List::nil|};

// exists [y:Bool] false → extract [y:Bool]
assert ⊢ {|$get_var_list|}
  (APP (APP exists
    (APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Bool)) {|eo::List::nil|}))
    false)
  ≡ APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Bool)) {|eo::List::nil|};

// Two variables: forall [x:Int, y:Int] true
assert ⊢ {|$get_var_list|}
  (APP (APP forall
    (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int))
      (APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Int)) {|eo::List::nil|})))
    true)
  ≡ APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int))
      (APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Int)) {|eo::List::nil|});

// ============================================================
// Quantifiers inherit Arith symbols
// ============================================================

assert ⊢ Int : Set;
assert ⊢ of_Z : τ (int ⤳ Int);
assert ⊢ {|eo::add|} (of_Z 1) (of_Z 2) ≡ of_Z 3;

// ============================================================
// eo::List operations
// ============================================================

// Empty variable list
assert ⊢ {|eo::List::nil|} : τ {|eo::List|};

// Concat two variable lists
assert ⊢ {|eo::List::concat|} {|eo::List::nil|} {|eo::List::nil|}
  ≡ {|eo::List::nil|};

// Concat non-empty with empty
assert ⊢ {|eo::List::concat|}
  (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int)) {|eo::List::nil|})
  {|eo::List::nil|}
  ≡ APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int)) {|eo::List::nil|};

// Concat two single-element lists
assert ⊢ {|eo::List::concat|}
  (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int)) {|eo::List::nil|})
  (APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Bool)) {|eo::List::nil|})
  ≡ APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int))
      (APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Bool)) {|eo::List::nil|});

// ============================================================
// eo::List::nth_type -- type of nth variable
// ============================================================

// nth_type of [x:Int] at index 0 = Int
assert ⊢ {|eo::List::nth_type|}
  (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int)) {|eo::List::nil|})
  0
  ≡ Int;

// nth_type of [x:Int, y:Bool] at index 0 = Int
assert ⊢ {|eo::List::nth_type|}
  (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int))
    (APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Bool)) {|eo::List::nil|}))
  0
  ≡ Int;

// nth_type of [x:Int, y:Bool] at index 1 = Bool
assert ⊢ {|eo::List::nth_type|}
  (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int))
    (APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Bool)) {|eo::List::nil|}))
  1
  ≡ Bool;

// ============================================================
// eo::List::nth -- get nth variable
// ============================================================

// nth of [x:Int] at index 0 = x
assert ⊢ {|eo::List::nth|} Int
  (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int)) {|eo::List::nil|})
  0
  ≡ {|eo::var|} "x" Int;

// nth of [x:Int, y:Bool] at index 0 = x
assert ⊢ {|eo::List::nth|} Int
  (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int))
    (APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Bool)) {|eo::List::nil|}))
  0
  ≡ {|eo::var|} "x" Int;

// nth of [x:Int, y:Bool] at index 1 = y
assert ⊢ {|eo::List::nth|} Bool
  (APP (APP ({|eo::List::cons|}) ({|eo::var|} "x" Int))
    (APP (APP ({|eo::List::cons|}) ({|eo::var|} "y" Bool)) {|eo::List::nil|}))
  1
  ≡ {|eo::var|} "y" Bool;

// ============================================================
// Boolean operations in Quantifiers context
// ============================================================

assert ⊢ {|eo::and|} true true ≡ true;
assert ⊢ {|eo::or|} false true ≡ true;
assert ⊢ {|eo::not|} true ≡ false;
assert ⊢ {|eo::eq|} (of_Z 1) (of_Z 1) ≡ true;
