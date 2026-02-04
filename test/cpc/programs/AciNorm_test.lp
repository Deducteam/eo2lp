require open cpc.theories.Arith;
require open cpc.programs.AciNorm;

// ============================================================
// Type declarations
// ============================================================

assert ⊢ {|@@aci_sorted|} : τ ((Int ⤳ (Int ⤳ Int)) ⤳ (Int ⤳ Int));

// ============================================================
// $aci_norm_eq -- syntactic equality (base rule: t ≡ t)
// ============================================================

assert ⊢ {|$aci_norm_eq|} true true ≡ true;
assert ⊢ {|$aci_norm_eq|} false false ≡ true;
assert ⊢ {|$aci_norm_eq|} (of_Z 1) (of_Z 1) ≡ true;
assert ⊢ {|$aci_norm_eq|} (of_Z 0) (of_Z 0) ≡ true;
assert ⊢ {|$aci_norm_eq|} (of_Z -5) (of_Z -5) ≡ true;

// Different terms → false
assert ⊢ {|$aci_norm_eq|} true false ≡ false;
assert ⊢ {|$aci_norm_eq|} (of_Z 1) (of_Z 2) ≡ false;
assert ⊢ {|$aci_norm_eq|} (of_Z 0) (of_Z 1) ≡ false;
assert ⊢ {|$aci_norm_eq|} (of_Z -1) (of_Z 1) ≡ false;

// ============================================================
// $aci_norm_eq -- @@aci_sorted match against raw term
// ============================================================

// @@aci_sorted(+, t) ≡ t → true (second rule)
assert ⊢ {|$aci_norm_eq|}
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+) (of_Z 5))
  (of_Z 5)
  ≡ true;

assert ⊢ {|$aci_norm_eq|}
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+) (of_Z 0))
  (of_Z 0)
  ≡ true;

// @@aci_sorted(+, t) vs different raw term → false
assert ⊢ {|$aci_norm_eq|}
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+) (of_Z 5))
  (of_Z 6)
  ≡ false;

// ============================================================
// $aci_norm_eq -- two @@aci_sorted terms (multiset equality)
// ============================================================

// Same singleton lists via @@aci_sorted
// @@aci_sorted(+, (+ 1 nil)) vs @@aci_sorted(+, (+ 1 nil))
assert ⊢ {|$aci_norm_eq|}
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+)
    (APP (APP (+) (of_Z 1)) ({|eo::nil|} (+) Int)))
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+)
    (APP (APP (+) (of_Z 1)) ({|eo::nil|} (+) Int)))
  ≡ true;

// Same elements, same order: (+ 1 (+ 2 nil)) vs (+ 1 (+ 2 nil))
assert ⊢ {|$aci_norm_eq|}
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+)
    (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int))))
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+)
    (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int))))
  ≡ true;

// Same elements, different order: (+ 1 (+ 2 nil)) vs (+ 2 (+ 1 nil))
// multiset equality, so should be true
assert ⊢ {|$aci_norm_eq|}
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+)
    (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int))))
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+)
    (APP (APP (+) (of_Z 2)) (APP (APP (+) (of_Z 1)) ({|eo::nil|} (+) Int))))
  ≡ true;

// Different elements: (+ 1 (+ 2 nil)) vs (+ 1 (+ 3 nil)) → false
assert ⊢ {|$aci_norm_eq|}
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+)
    (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int))))
  (@{|@@aci_sorted|} (Int ⤳ (Int ⤳ Int)) Int (+)
    (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 3)) ({|eo::nil|} (+) Int))))
  ≡ false;

// ============================================================
// $is_aci_norm -- combining aci_norm_eq checks
// ============================================================

// All same: is_aci_norm a a a a = true
assert ⊢ {|$is_aci_norm|} (of_Z 1) (of_Z 1) (of_Z 1) (of_Z 1) ≡ true;

// an == b: is_aci_norm a b an b where an=b → true
assert ⊢ {|$is_aci_norm|} (of_Z 1) (of_Z 2) (of_Z 2) (of_Z 3) ≡ true;

// bn == a: is_aci_norm a b c a → true
assert ⊢ {|$is_aci_norm|} (of_Z 1) (of_Z 2) (of_Z 3) (of_Z 1) ≡ true;

// an == bn: is_aci_norm a b c c → true
assert ⊢ {|$is_aci_norm|} (of_Z 1) (of_Z 2) (of_Z 3) (of_Z 3) ≡ true;

// All different, none match → false
assert ⊢ {|$is_aci_norm|} (of_Z 1) (of_Z 2) (of_Z 3) (of_Z 4) ≡ false;

// ============================================================
// $get_a_norm -- associativity normalization (flattening)
// ============================================================

// Singleton: (+ 1 nil) → (+ 1 nil) (unchanged)
assert ⊢ {|$get_a_norm|}
  (APP (APP (+) (of_Z 1)) ({|eo::nil|} (+) Int))
  ≡ of_Z 1;

// Flat list: (+ 1 (+ 2 nil)) stays flat
assert ⊢ {|$get_a_norm|}
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int)))
  ≡ APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int));

// Nested: (+ (+ 1 (+ 2 nil)) (+ 3 nil)) → (+ 1 (+ 2 (+ 3 nil)))
assert ⊢ {|$get_a_norm|}
  (APP (APP (+)
    (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int))))
    (APP (APP (+) (of_Z 3)) ({|eo::nil|} (+) Int)))
  ≡ APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) (APP (APP (+) (of_Z 3)) ({|eo::nil|} (+) Int)));

// ============================================================
// $get_ai_norm -- associativity+idempotency normalization
// ============================================================

// Singleton
assert ⊢ {|$get_ai_norm|}
  (APP (APP (+) (of_Z 1)) ({|eo::nil|} (+) Int))
  ≡ of_Z 1;

// Two distinct elements stay
assert ⊢ {|$get_ai_norm|}
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int)))
  ≡ APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 2)) ({|eo::nil|} (+) Int));

// Duplicate removal: (+ 1 (+ 1 nil)) → 1
assert ⊢ {|$get_ai_norm|}
  (APP (APP (+) (of_Z 1)) (APP (APP (+) (of_Z 1)) ({|eo::nil|} (+) Int)))
  ≡ of_Z 1;

// ============================================================
// Arithmetic operations accessible in AciNorm context
// ============================================================

assert ⊢ {|eo::add|} (of_Z 1) (of_Z 2) ≡ of_Z 3;
assert ⊢ {|eo::nil|} (+) Int ≡ of_Z 0;
assert ⊢ {|eo::eq|} (of_Z 1) (of_Z 1) ≡ true;
