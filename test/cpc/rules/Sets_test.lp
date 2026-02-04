require open cpc.rules.Sets;

symbol x : τ Int;
symbol y : τ Int;
symbol s : τ ({|eo::Set|} Int);
symbol t : τ ({|eo::Set|} Int);

// ============================================================
// Programs: $set_union_to_list
// ============================================================

// Empty set → nil
assert ⊢ {|$set_union_to_list|} (@{|set.empty|} Int) ≡ {|eo::List::nil|};

// Singleton → cons
assert ⊢ {|$set_union_to_list|} (@{|set.singleton|} Int x)
         ≡ {|eo::List::cons|} x {|eo::List::nil|};

// Union of singletons
assert ⊢ {|$set_union_to_list|} ({|set.union|} ({|set.singleton|} x) (@{|set.empty|} Int))
         ≡ {|eo::cons|} {|eo::List::cons|} x ({|$set_union_to_list|} (@{|set.empty|} Int));

// ============================================================
// Programs: $eval_sets_op (union)
// ============================================================

// Union of two singleton-unions: concatenates lists
assert ⊢ {|$eval_sets_op|} ({|set.union|} ({|set.singleton|} x) ({|set.singleton|} y))
         ≡ {|eo::List::concat|} ({|$set_union_to_list|} ({|set.singleton|} x))
                                 ({|$set_union_to_list|} ({|set.singleton|} y));

// ============================================================
// Proof rules: sets_singleton_inj
// ============================================================

// If {a} = {b}, then a = b
assert ⊢ sets_singleton_inj
         : Proof (APP (APP (@= ({|eo::Set|} Int)) ({|set.singleton|} x)) ({|set.singleton|} y))
           → Proof (APP (APP = x) y);

// ============================================================
// Proof rules: sets_ext
// ============================================================

// If s ≠ t, then membership differs at the diff witness
assert ⊢ sets_ext
         : Proof (APP not (APP (APP (@= ({|eo::Set|} Int)) s) t))
           → Proof (APP not (APP (APP = ({|set.member|} ({|@sets_deq_diff|} s t) s))
                                       ({|set.member|} ({|@sets_deq_diff|} s t) t)));

// ============================================================
// Proof rules: sets-eval-op
// ============================================================

// sets-eval-op asserts set equality
assert ⊢ sets-eval-op (APP (APP (@= ({|eo::Set|} Int)) s) t)
         : Proof (APP (APP = s) t);
