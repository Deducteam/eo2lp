require open cpc.rules.Quantifiers;

symbol p : τ Bool;
symbol q : τ Bool;
symbol x : τ Int;
symbol y : τ Int;

// Variable list for a single Int variable
symbol xs : τ {|eo::List|};

// ============================================================
// Proof rules: instantiate
// ============================================================

// instantiate type-checks: from forall xs. F, get F[xs/ts]
assert ⊢ instantiate ({|eo::List::cons|} (of_Z 0) {|eo::List::nil|})
         : Proof (APP (APP forall xs) p)
           → Proof ({|$substitute_simul|} p xs ({|eo::List::cons|} (of_Z 0) {|eo::List::nil|}));

// ============================================================
// Programs: $mk_skolems
// ============================================================

// Base case: empty variable list
assert ⊢ {|$mk_skolems|} {|eo::List::nil|} p (of_Z 0) ≡ {|eo::List::nil|};

// ============================================================
// Proof rules: skolemize
// ============================================================

// skolemize: from ¬∀x.G, derive ¬G[x/sk]
assert ⊢ skolemize
         : Proof (APP not (APP (APP forall xs) p))
           → Proof ({|$substitute_simul|} (APP not p) xs
                    ({|$mk_skolems|} xs (APP (APP forall xs) p) (of_Z 0)));

// ============================================================
// Proof rules: alpha_equiv
// ============================================================

// alpha_equiv: t = t[vs/ts]
assert ⊢ alpha_equiv p xs ({|eo::List::cons|} (of_Z 0) {|eo::List::nil|})
         : Proof (APP (APP = p)
                 ({|$substitute_simul|} p xs ({|eo::List::cons|} (of_Z 0) {|eo::List::nil|})));

// ============================================================
// Programs: $mk_quant_unused_vars_rec
// ============================================================

// Empty list returns empty
assert ⊢ {|$mk_quant_unused_vars_rec|} {|eo::List::nil|} p ≡ {|eo::List::nil|};

// ============================================================
// Programs: $mk_quant
// ============================================================

// Empty variable list: forall/exists with no vars is just F
assert ⊢ {|$mk_quant|} forall {|eo::List::nil|} p ≡ p;

// Non-empty: wraps with quantifier
assert ⊢ {|$mk_quant|} forall xs p ≡ APP (APP forall xs) p;

// ============================================================
// Programs: $mk_quant_merge_prenex
// ============================================================

// Non-quantified body: wraps with accumulated variables
assert ⊢ {|$mk_quant_merge_prenex|} forall p xs ≡ APP (APP forall xs) p;

// Nested quantifier: merges variable lists
assert ⊢ {|$mk_quant_merge_prenex|} forall (APP (APP forall xs) p) {|eo::List::nil|}
         ≡ {|$mk_quant_merge_prenex|} forall p ({|eo::List::concat|} {|eo::List::nil|} xs);

// ============================================================
// Programs: $mk_quant_miniscope_and
// ============================================================

// Base case
assert ⊢ {|$mk_quant_miniscope_and|} xs true ≡ true;

// Single conjunct: wraps each with forall
assert ⊢ {|$mk_quant_miniscope_and|} xs (APP (APP and p) true)
         ≡ {|eo::cons|} and (APP (APP forall xs) p) ({|$mk_quant_miniscope_and|} xs true);

// ============================================================
// Proof rules: quant_var_reordering
// ============================================================

assert ⊢ quant_var_reordering (APP (APP (@= Bool) (APP (APP forall xs) p)) (APP (APP forall xs) p))
         : Proof (APP (APP = (APP (APP forall xs) p)) (APP (APP forall xs) p));

// ============================================================
// Proof rules: exists-elim
// ============================================================

assert ⊢ exists-elim (APP (APP (@= Bool) (APP (APP exists xs) p)) (APP not (APP (APP forall xs) (APP not p))))
         : Proof (APP (APP = (APP (APP exists xs) p)) (APP not (APP (APP forall xs) (APP not p))));

// ============================================================
// Proof rules: quant-unused-vars
// ============================================================

assert ⊢ quant-unused-vars (APP (APP (@= Bool) (APP (APP forall xs) p)) q)
         : Proof (APP (APP = (APP (APP forall xs) p)) q);

// ============================================================
// Proof rules: quant-merge-prenex
// ============================================================

assert ⊢ quant-merge-prenex (APP (APP (@= Bool) (APP (APP forall xs) p)) q)
         : Proof (APP (APP = (APP (APP forall xs) p)) q);

// ============================================================
// Proof rules: quant-miniscope-and
// ============================================================

assert ⊢ quant-miniscope-and (APP (APP (@= Bool) (APP (APP forall xs) p)) q)
         : Proof (APP (APP = (APP (APP forall xs) p)) q);

// ============================================================
// Proof rules: quant-miniscope-or
// ============================================================

assert ⊢ quant-miniscope-or (APP (APP (@= Bool) (APP (APP forall xs) p)) q)
         : Proof (APP (APP = (APP (APP forall xs) p)) q);

// ============================================================
// Proof rules: quant-miniscope-ite
// ============================================================

symbol c : τ Bool;
assert ⊢ quant-miniscope-ite (APP (APP (@= Bool) (APP (APP forall xs) (ite c p q)))
                              (ite c (APP (APP forall xs) p) (APP (APP forall xs) q)))
         : Proof (APP (APP = (APP (APP forall xs) (ite c p q)))
                 (ite c (APP (APP forall xs) p) (APP (APP forall xs) q)));
