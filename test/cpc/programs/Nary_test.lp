require open cpc.programs.Nary;

// ============================================================
// $assoc_nil_nth_type -- type of nth element in n-ary term
// ============================================================

// Single element (+ 10 nil): nth_type at 0 = Int
assert ⊢ {|$assoc_nil_nth_type|} (+)
  (APP (APP (+) (of_Z 10)) ({|eo::nil|} (+) Int))
  (of_Z 0)
  ≡ Int;

// Two elements (+ 10 (+ 20 nil)): nth_type at 0 = Int
assert ⊢ {|$assoc_nil_nth_type|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) ({|eo::nil|} (+) Int)))
  (of_Z 0)
  ≡ Int;

// Two elements: nth_type at 1 = Int
assert ⊢ {|$assoc_nil_nth_type|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) ({|eo::nil|} (+) Int)))
  (of_Z 1)
  ≡ Int;

// Three elements: nth_type at 2 = Int
assert ⊢ {|$assoc_nil_nth_type|} (+)
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) (APP (APP (+) (of_Z 3)) ({|eo::nil|} (+) Int))))
  (of_Z 2)
  ≡ Int;

// ============================================================
// $assoc_nil_nth -- get nth element from n-ary term
// ============================================================

// Single element (+ 10 nil): nth at 0 = 10
assert ⊢ {|$assoc_nil_nth|} (+)
  (APP (APP (+) (of_Z 10)) ({|eo::nil|} (+) Int))
  (of_Z 0)
  ≡ of_Z 10;

// Two elements (+ 10 (+ 20 nil)): nth at 0 = 10
assert ⊢ {|$assoc_nil_nth|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) ({|eo::nil|} (+) Int)))
  (of_Z 0)
  ≡ of_Z 10;

// Two elements: nth at 1 = 20
assert ⊢ {|$assoc_nil_nth|} (+)
  (APP (APP (+) (of_Z 10)) (APP (APP (+) (of_Z 20)) ({|eo::nil|} (+) Int)))
  (of_Z 1)
  ≡ of_Z 20;

// Three elements (+ 1 (+ 2 (+ 3 nil))): nth at 0, 1, 2
assert ⊢ {|$assoc_nil_nth|} (+)
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) (APP (APP (+) (of_Z 3)) ({|eo::nil|} (+) Int))))
  (of_Z 0)
  ≡ of_Z 1;

assert ⊢ {|$assoc_nil_nth|} (+)
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) (APP (APP (+) (of_Z 3)) ({|eo::nil|} (+) Int))))
  (of_Z 1)
  ≡ of_Z 2;

assert ⊢ {|$assoc_nil_nth|} (+)
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) (APP (APP (+) (of_Z 3)) ({|eo::nil|} (+) Int))))
  (of_Z 2)
  ≡ of_Z 3;

// ============================================================
// $assoc_nil_nth with * operator
// ============================================================

// (* 5 (* 6 nil)): nth at 0 = 5, nth at 1 = 6
assert ⊢ {|$assoc_nil_nth|} (*)
  (APP (APP (*) (of_Z 5)) (APP (APP (*) (of_Z 6)) ({|eo::nil|} (*) Int)))
  (of_Z 0)
  ≡ of_Z 5;

assert ⊢ {|$assoc_nil_nth|} (*)
  (APP (APP (*) (of_Z 5)) (APP (APP (*) (of_Z 6)) ({|eo::nil|} (*) Int)))
  (of_Z 1)
  ≡ of_Z 6;

// $assoc_nil_nth_type with *: all Int
assert ⊢ {|$assoc_nil_nth_type|} (*)
  (APP (APP (*) (of_Z 5)) (APP (APP (*) (of_Z 6)) ({|eo::nil|} (*) Int)))
  (of_Z 0)
  ≡ Int;

assert ⊢ {|$assoc_nil_nth_type|} (*)
  (APP (APP (*) (of_Z 5)) (APP (APP (*) (of_Z 6)) ({|eo::nil|} (*) Int)))
  (of_Z 1)
  ≡ Int;

// ============================================================
// $assoc_nil_nth with negative literal values
// ============================================================

assert ⊢ {|$assoc_nil_nth|} (+)
  (APP (APP (+) (of_Z -10)) (APP (APP (+) (of_Z -20)) ({|eo::nil|} (+) Int)))
  (of_Z 0)
  ≡ of_Z -10;

assert ⊢ {|$assoc_nil_nth|} (+)
  (APP (APP (+) (of_Z -10)) (APP (APP (+) (of_Z -20)) ({|eo::nil|} (+) Int)))
  (of_Z 1)
  ≡ of_Z -20;

// ============================================================
// Arith symbols accessible in Nary context
// ============================================================

assert ⊢ Int : Set;
assert ⊢ {|eo::add|} (of_Z 1) (of_Z 2) ≡ of_Z 3;
assert ⊢ {|eo::nil|} (+) Int ≡ of_Z 0;
assert ⊢ {|eo::nil|} (*) Int ≡ of_Z 1;
