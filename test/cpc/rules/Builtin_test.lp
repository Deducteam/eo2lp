require open cpc.rules.Builtin;

// ============================================================
// Programs: $extract_antec_rec
// ============================================================

// Base case: conclusion matches
assert ⊢ {|$extract_antec_rec|} true true ≡ true;

// Recursive case: extract from implication chain
// (=> F1 F2) with conclusion F2: returns F1
assert ⊢ {|$extract_antec_rec|} (APP (APP => true) false) false
         ≡ {|eo::cons|} and true ({|$extract_antec_rec|} false false);

// ============================================================
// Programs: $extract_antec
// ============================================================

// Direct implication: (=> F C) with conclusion C returns F
assert ⊢ {|$extract_antec|} (APP (APP => true) false) false ≡ true;

// Fallthrough delegates to $extract_antec_rec
assert ⊢ {|$extract_antec|} true true ≡ {|$extract_antec_rec|} true true;

// ============================================================
// Programs: $run_process_scope
// ============================================================

// With false conclusion: negate the antecedent
assert ⊢ {|$run_process_scope|} true false ≡ APP not ({|$extract_antec|} true false);

// With non-false conclusion: implication form
assert ⊢ {|$run_process_scope|} (APP (APP => true) true) true
         ≡ APP (APP => ({|$extract_antec|} (APP (APP => true) true) true)) true;

// ============================================================
// Proof rules: scope
// ============================================================

// scope type-checks: given Proof G, produces Proof (=> F G)
assert ⊢ scope true : Proof true → Proof (APP (APP => true) true);

// ============================================================
// Proof rules: process_scope
// ============================================================

// process_scope type-checks
assert ⊢ process_scope false
         : Proof true → Proof ({|$run_process_scope|} true false);

// ============================================================
// Proof rules: ite_eq
// ============================================================

// ite_eq on a boolean ite
assert ⊢ ite_eq (@ite Bool true true false)
         : Proof (let k ≔ ite true true false in
                  ite true (APP (APP = k) true) (APP (APP = k) false));

// ============================================================
// Proof rules: proof_nil and proof_cons
// ============================================================

// proof_nil proves true
assert ⊢ proof_nil : Proof true;

// proof_cons conjoins two proofs
assert ⊢ proof_cons
         : Proof true → Proof true → Proof (APP (APP and true) true);
