require open cpc.rules.Booleans;

// ============================================================
// Programs: $to_clause
// ============================================================

// false stays false
assert ⊢ {|$to_clause|} false ≡ false;

// Single formula gets or-false wrapper
assert ⊢ {|$to_clause|} true ≡ APP (APP or true) false;

// Already-or stays as-is
symbol p : τ Bool;
symbol q : τ Bool;
symbol r : τ Bool;
assert ⊢ {|$to_clause|} (APP (APP or p) false) ≡ APP (APP or p) false;

// ============================================================
// Programs: $from_clause
// ============================================================

// Strips trailing false from singleton clause
assert ⊢ {|$from_clause|} (APP (APP or true) false) ≡ true;

// Non-clause passthrough
assert ⊢ {|$from_clause|} true ≡ true;
assert ⊢ {|$from_clause|} false ≡ false;

// Multi-element clause stays
assert ⊢ {|$from_clause|} (APP (APP or p) (APP (APP or q) false))
         ≡ APP (APP or p) (APP (APP or q) false);

// ============================================================
// Programs: $lower_not_and
// ============================================================

// Base case: not-and of true => false
assert ⊢ {|$lower_not_and|} true ≡ false;

// Single conjunct
assert ⊢ {|$lower_not_and|} (APP (APP and p) true)
         ≡ {|eo::cons|} or (APP not p) ({|$lower_not_and|} true);

// ============================================================
// Proof rules: split
// ============================================================

// split(F) proves F ∨ ¬F
assert ⊢ split true : Proof (APP (APP or true) (APP (APP or (APP not true)) false));
assert ⊢ split p : Proof (APP (APP or p) (APP (APP or (APP not p)) false));

// ============================================================
// Proof rules: and_elim
// ============================================================

// Extract ith conjunct
assert ⊢ and_elim (of_Z 0)
         : Proof (APP (APP and p) (APP (APP and q) true))
           → Proof ({|eo::list_nth|} and (APP (APP and p) (APP (APP and q) true)) (of_Z 0));

// ============================================================
// Proof rules: and_intro
// ============================================================

assert ⊢ and_intro true : Proof true → Proof true;

// ============================================================
// Proof rules: not_or_elim
// ============================================================

// From ¬(F₁ ∨ F₂), extract ¬Fᵢ
assert ⊢ not_or_elim (of_Z 0)
         : Proof (APP not (APP (APP or p) (APP (APP or q) false)))
           → Proof (APP not ({|eo::list_nth|} or (APP (APP or p) (APP (APP or q) false)) (of_Z 0)));

// ============================================================
// Proof rules: resolution
// ============================================================

// resolution type-checks with explicit type annotation
symbol c1 : τ Bool;
symbol c2 : τ Bool;
assert ⊢ resolution true p
         : Proof c1 → Proof c2 → Proof ({|$resolve|} c1 c2 true p);

// ============================================================
// Proof rules: eq_resolve
// ============================================================

// From F and F = G, derive G
assert ⊢ eq_resolve
         : Proof p → Proof (APP (APP (@= Bool) p) q) → Proof q;

// ============================================================
// Proof rules: modus_ponens
// ============================================================

// From F and F => G, derive G
assert ⊢ modus_ponens
         : Proof p → Proof (APP (APP => p) q) → Proof q;

// ============================================================
// Proof rules: not_not_elim
// ============================================================

// ¬¬F → F
assert ⊢ not_not_elim
         : Proof (APP not (APP not p)) → Proof p;

// ============================================================
// Proof rules: contra
// ============================================================

// F and ¬F → false
assert ⊢ contra : Proof p → Proof (APP not p) → Proof false;

// ============================================================
// Proof rules: implies_elim
// ============================================================

// (F₁ => F₂) → (¬F₁ ∨ F₂)
assert ⊢ implies_elim
         : Proof (APP (APP => p) q)
           → Proof (APP (APP or (APP not p)) (APP (APP or q) false));

// ============================================================
// Proof rules: not_implies_elim1 / not_implies_elim2
// ============================================================

assert ⊢ not_implies_elim1
         : Proof (APP not (APP (APP => p) q)) → Proof p;
assert ⊢ not_implies_elim2
         : Proof (APP not (APP (APP => p) q)) → Proof (APP not q);

// ============================================================
// Proof rules: equiv_elim1 / equiv_elim2
// ============================================================

assert ⊢ equiv_elim1
         : Proof (APP (APP (@= Bool) p) q)
           → Proof (APP (APP or (APP not p)) (APP (APP or q) false));
assert ⊢ equiv_elim2
         : Proof (APP (APP (@= Bool) p) q)
           → Proof (APP (APP or p) (APP (APP or (APP not q)) false));

// ============================================================
// Proof rules: not_equiv_elim1 / not_equiv_elim2
// ============================================================

assert ⊢ not_equiv_elim1
         : Proof (APP not (APP (APP (@= Bool) p) q))
           → Proof (APP (APP or p) (APP (APP or q) false));
assert ⊢ not_equiv_elim2
         : Proof (APP not (APP (APP (@= Bool) p) q))
           → Proof (APP (APP or (APP not p)) (APP (APP or (APP not q)) false));

// ============================================================
// Proof rules: xor_elim1 / xor_elim2
// ============================================================

assert ⊢ xor_elim1
         : Proof (APP (APP xor q) p)
           → Proof (APP (APP or p) (APP (APP or q) false));
assert ⊢ xor_elim2
         : Proof (APP (APP xor q) p)
           → Proof (APP (APP or (APP not p)) (APP (APP or (APP not q)) false));

// ============================================================
// Proof rules: not_xor_elim1 / not_xor_elim2
// ============================================================

assert ⊢ not_xor_elim1
         : Proof (APP not (APP (APP xor q) p))
           → Proof (APP (APP or p) (APP (APP or (APP not q)) false));
assert ⊢ not_xor_elim2
         : Proof (APP not (APP (APP xor q) p))
           → Proof (APP (APP or (APP not p)) (APP (APP or q) false));

// ============================================================
// Proof rules: ite_elim1 / ite_elim2
// ============================================================

assert ⊢ ite_elim1
         : Proof (ite p q r)
           → Proof (APP (APP or (APP not p)) (APP (APP or q) false));
assert ⊢ ite_elim2
         : Proof (ite p q r)
           → Proof (APP (APP or p) (APP (APP or r) false));

// ============================================================
// Proof rules: not_ite_elim1 / not_ite_elim2
// ============================================================

assert ⊢ not_ite_elim1
         : Proof (APP not (ite p q r))
           → Proof (APP (APP or (APP not p)) (APP (APP or (APP not q)) false));
assert ⊢ not_ite_elim2
         : Proof (APP not (ite p q r))
           → Proof (APP (APP or p) (APP (APP or (APP not r)) false));

// ============================================================
// Proof rules: not_and
// ============================================================

assert ⊢ not_and
         : Proof (APP not (APP (APP and p) (APP (APP and q) true)))
           → Proof ({|$lower_not_and|} (APP (APP and p) (APP (APP and q) true)));

// ============================================================
// Proof rules: cnf_and_pos / cnf_and_neg
// ============================================================

assert ⊢ cnf_and_pos (APP (APP and p) (APP (APP and q) true)) (of_Z 0)
         : Proof (APP (APP or (APP not (APP (APP and p) (APP (APP and q) true))))
                 (APP (APP or ({|eo::list_nth|} and (APP (APP and p) (APP (APP and q) true)) (of_Z 0))) false));

symbol fs : τ Bool;
assert ⊢ cnf_and_neg fs
         : Proof ({|eo::cons|} or fs ({|$lower_not_and|} fs));

// ============================================================
// Proof rules: cnf_or_pos / cnf_or_neg
// ============================================================

assert ⊢ cnf_or_pos (APP (APP or p) (APP (APP or q) false))
         : Proof (APP (APP or (APP not (APP (APP or p) (APP (APP or q) false))))
                 (APP (APP or p) (APP (APP or q) false)));

assert ⊢ cnf_or_neg (APP (APP or p) (APP (APP or q) false)) (of_Z 0)
         : Proof (APP (APP or (APP (APP or p) (APP (APP or q) false)))
                 (APP (APP or (APP not ({|eo::list_nth|} or (APP (APP or p) (APP (APP or q) false)) (of_Z 0)))) false));

// ============================================================
// Proof rules: cnf_implies_pos
// ============================================================

assert ⊢ cnf_implies_pos (APP (APP => p) q)
         : Proof (APP (APP or (APP not (APP (APP => p) q)))
                 (APP (APP or (APP not p)) (APP (APP or q) false)));

// ============================================================
// Proof rules: cnf_ite_pos1
// ============================================================

assert ⊢ cnf_ite_pos1 (@ite Bool p q r)
         : Proof (APP (APP or (APP not (ite p q r)))
                 (APP (APP or (APP not p)) (APP (APP or q) false)));

// ============================================================
// Proof rules: factoring / reordering
// ============================================================

symbol cl : τ Bool;
assert ⊢ factoring
         : Proof cl → Proof ({|$from_clause|} ({|eo::list_setof|} or cl));

assert ⊢ reordering (APP (APP or q) (APP (APP or p) false))
         : Proof (APP (APP or p) (APP (APP or q) false))
           → Proof (APP (APP or q) (APP (APP or p) false));
