require open cpc.rules.Uf;

symbol x : τ Int;
symbol y : τ Int;
symbol z : τ Int;
symbol p : τ Bool;
symbol q : τ Bool;
symbol f : τ (Int ⤳ Int);

// ============================================================
// Programs: $mk_symm
// ============================================================

// Flip positive equality
assert ⊢ {|$mk_symm|} (APP (APP (@= Int) x) y) ≡ APP (APP = y) x;

// Flip negated equality
assert ⊢ {|$mk_symm|} (APP not (APP (APP (@= Int) x) y))
         ≡ APP not (APP (APP = y) x);

// Flip boolean equality
assert ⊢ {|$mk_symm|} (APP (APP (@= Bool) p) q) ≡ APP (APP = q) p;

// ============================================================
// Programs: $mk_trans
// ============================================================

// Base case: no more equalities
assert ⊢ {|$mk_trans|} x y true ≡ APP (APP = x) y;

// ============================================================
// Programs: $mk_cong_rhs
// ============================================================

// Base case: function with no more equalities
assert ⊢ {|$mk_cong_rhs|} f true ≡ f;

// ============================================================
// Programs: $mk_distinct_elim
// ============================================================

// Two-element distinct list
assert ⊢ {|$mk_distinct_elim|} (APP distinct ({|eo::List::cons|} x ({|eo::List::cons|} y {|eo::List::nil|})))
         ≡ {|$mk_distinct_elim_rec|} x ({|eo::List::cons|} y {|eo::List::nil|}) ({|$mk_distinct_elim|} (APP distinct ({|eo::List::cons|} y {|eo::List::nil|})));

// ============================================================
// Programs: $mk_distinct_elim_rec
// ============================================================

// Base case: empty list
assert ⊢ {|$mk_distinct_elim_rec|} x {|eo::List::nil|} true ≡ true;

// One element: produces inequality
assert ⊢ {|$mk_distinct_elim_rec|} x ({|eo::List::cons|} y {|eo::List::nil|}) true
         ≡ {|eo::cons|} and (APP not (APP (APP = x) y))
           ({|$mk_distinct_elim_rec|} x {|eo::List::nil|} true);

// ============================================================
// Proof rules: refl
// ============================================================

assert ⊢ refl (of_Z 42) : Proof (APP (APP = (of_Z 42)) (of_Z 42));
assert ⊢ refl true : Proof (APP (APP = true) true);
assert ⊢ refl x : Proof (APP (APP = x) x);

// ============================================================
// Proof rules: symm
// ============================================================

assert ⊢ symm : Proof (APP (APP (@= Int) x) y) → Proof ({|$mk_symm|} (APP (APP (@= Int) x) y));

// ============================================================
// Proof rules: cong
// ============================================================

// cong on a function application with one equality
assert ⊢ cong (APP (APP (@= Int) x) y) (APP f x)
         : Proof (APP (APP (@= Int) x) y)
           → Proof (APP (APP = (APP f x)) ({|$mk_cong_rhs|} (APP f x) ({|eo::list_rev|} and (APP (APP (@= Int) x) y))));

// ============================================================
// Proof rules: nary_cong
// ============================================================

// nary_cong applies elementwise equalities to n-ary terms
assert ⊢ nary_cong (APP (APP (@= Int) x) y) (APP (APP + x) (APP (APP + z) (of_Z 0)))
         : Proof (APP (APP (@= Int) x) y)
           → Proof (APP (APP = (APP (APP + x) (APP (APP + z) (of_Z 0))))
                   ({|$mk_nary_cong_rhs|} (APP (APP + x) (APP (APP + z) (of_Z 0))) (APP (APP (@= Int) x) y)));

// ============================================================
// Proof rules: true_intro / true_elim
// ============================================================

assert ⊢ true_intro : Proof p → Proof (APP (APP = p) true);
assert ⊢ true_elim : Proof (APP (APP (@= Bool) p) true) → Proof p;

// ============================================================
// Proof rules: false_intro / false_elim
// ============================================================

assert ⊢ false_intro : Proof (APP not p) → Proof (APP (APP = p) false);
assert ⊢ false_elim : Proof (APP (APP (@= Bool) p) false) → Proof (APP not p);

// ============================================================
// Proof rules: distinct-elim
// ============================================================

// distinct-elim on two elements is equivalence to their inequality
assert ⊢ distinct-elim (APP (APP (@= Bool) (APP distinct ({|eo::List::cons|} x ({|eo::List::cons|} y {|eo::List::nil|})))) (APP not (APP (APP = x) y)))
         : Proof (APP (APP = (APP distinct ({|eo::List::cons|} x ({|eo::List::cons|} y {|eo::List::nil|})))) (APP not (APP (APP = x) y)));
