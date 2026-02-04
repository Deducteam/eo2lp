require open cpc.rules.Arith;

// ============================================================
// Programs: $arith_rel_sum
// ============================================================

// < + < = <
assert ⊢ {|$arith_rel_sum|} (<) (<) (of_Z 1) (of_Z 2)
         ≡ APP (APP < (of_Z 1)) (of_Z 2);

// <= + <= = <=
assert ⊢ {|$arith_rel_sum|} (<=) (<=) (of_Z 1) (of_Z 2)
         ≡ APP (APP <= (of_Z 1)) (of_Z 2);

// < + <= = <
assert ⊢ {|$arith_rel_sum|} (<) (<=) (of_Z 1) (of_Z 2)
         ≡ APP (APP < (of_Z 1)) (of_Z 2);

// <= + < = <
assert ⊢ {|$arith_rel_sum|} (<=) (<) (of_Z 1) (of_Z 2)
         ≡ APP (APP < (of_Z 1)) (of_Z 2);

// = + = = <=
assert ⊢ {|$arith_rel_sum|} ((@= Int)) ((@= Int)) (of_Z 1) (of_Z 2)
         ≡ APP (APP <= (of_Z 1)) (of_Z 2);

// < + = = <
assert ⊢ {|$arith_rel_sum|} (<) ((@= Int)) (of_Z 1) (of_Z 2)
         ≡ APP (APP < (of_Z 1)) (of_Z 2);

// = + < = <
assert ⊢ {|$arith_rel_sum|} ((@= Int)) (<) (of_Z 1) (of_Z 2)
         ≡ APP (APP < (of_Z 1)) (of_Z 2);

// <= + = = <=
assert ⊢ {|$arith_rel_sum|} (<=) ((@= Int)) (of_Z 1) (of_Z 2)
         ≡ APP (APP <= (of_Z 1)) (of_Z 2);

// = + <= = <=
assert ⊢ {|$arith_rel_sum|} ((@= Int)) (<=) (of_Z 1) (of_Z 2)
         ≡ APP (APP <= (of_Z 1)) (of_Z 2);

// ============================================================
// Programs: $arith_rel_inv
// ============================================================

// inv(=) = =
symbol x : τ Int;
symbol y : τ Int;
assert ⊢ {|$arith_rel_inv|} ((@= Int)) x y ≡ APP (APP = x) y;

// inv(<) = >
assert ⊢ {|$arith_rel_inv|} (<) x y ≡ APP (APP > x) y;

// inv(<=) = >=
assert ⊢ {|$arith_rel_inv|} (<=) x y ≡ APP (APP >= x) y;

// inv(>) = <
assert ⊢ {|$arith_rel_inv|} (>) x y ≡ APP (APP < x) y;

// inv(>=) = <=
assert ⊢ {|$arith_rel_inv|} (>=) x y ≡ APP (APP <= x) y;

// ============================================================
// Programs: $arith_rel_neg
// ============================================================

// neg(<) = >=
assert ⊢ {|$arith_rel_neg|} (<) x y ≡ APP (APP >= x) y;

// neg(<=) = >
assert ⊢ {|$arith_rel_neg|} (<=) x y ≡ APP (APP > x) y;

// neg(>) = <=
assert ⊢ {|$arith_rel_neg|} (>) x y ≡ APP (APP <= x) y;

// neg(>=) = <
assert ⊢ {|$arith_rel_neg|} (>=) x y ≡ APP (APP < x) y;

// ============================================================
// Programs: $arith_normalize_lit
// ============================================================

// Positive literal passthrough
assert ⊢ {|$arith_normalize_lit|} (APP (APP < x) y) ≡ APP (APP < x) y;

// Negated literal uses rel_neg
assert ⊢ {|$arith_normalize_lit|} (APP not (APP (APP < x) y))
         ≡ {|$arith_rel_neg|} (<) x y;

// Double negation cancels
assert ⊢ {|$arith_normalize_lit|} (APP not (APP not (APP (APP < x) y)))
         ≡ APP (APP < x) y;

// ============================================================
// Programs: $arith_rel_trichotomy
// ============================================================

// = and < => >
assert ⊢ {|$arith_rel_trichotomy|} ((@= Int)) (<) x y ≡ APP (APP > x) y;

// = and > => <
assert ⊢ {|$arith_rel_trichotomy|} ((@= Int)) (>) x y ≡ APP (APP < x) y;

// > and < => =
assert ⊢ {|$arith_rel_trichotomy|} (>) (<) x y ≡ APP (APP = x) y;

// < and > => =
assert ⊢ {|$arith_rel_trichotomy|} (<) (>) x y ≡ APP (APP = x) y;

// > and = => <
assert ⊢ {|$arith_rel_trichotomy|} (>) ((@= Int)) x y ≡ APP (APP < x) y;

// < and = => >
assert ⊢ {|$arith_rel_trichotomy|} (<) ((@= Int)) x y ≡ APP (APP > x) y;

// ============================================================
// Programs: $greatest_int_lt / $least_int_gt
// ============================================================

assert ⊢ {|$greatest_int_lt|} (of_Z 5) ≡ {|eo::add|} (of_Z -1) (of_Z 5);
assert ⊢ {|$least_int_gt|} (of_Z 5) ≡ {|eo::add|} (of_Z 1) (of_Z 5);

// ============================================================
// Proof rules: arith_sum_ub
// ============================================================

// arith_sum_ub type-checks on a conjunction of inequalities
assert ⊢ arith_sum_ub (APP (APP and (APP (APP < x) y)) true)
         : Proof (APP (APP and (APP (APP < x) y)) true)
           → Proof ({|$mk_arith_sum_ub|} ({|eo::list_rev|} and (APP (APP and (APP (APP < x) y)) true)) (APP (APP = (of_Z 0)) (of_Z 0)));

// ============================================================
// Proof rules: int_tight_ub / int_tight_lb
// ============================================================

assert ⊢ int_tight_ub
         : Proof (APP (APP < x) y) → Proof (APP (APP <= x) ({|$greatest_int_lt|} y));

assert ⊢ int_tight_lb
         : Proof (APP (APP > x) y) → Proof (APP (APP >= x) ({|$least_int_gt|} y));

// ============================================================
// Proof rules: arith_mult_pos / arith_mult_neg
// ============================================================

symbol m : τ Int;
assert ⊢ arith_mult_pos m (APP (APP < x) y)
         : Proof (APP (APP => (APP (APP and (APP (APP > m) (of_Z 0)))
                              (APP (APP and (APP (APP < x) y)) true)))
                 ({|$mk_arith_mult_pos|} m (APP (APP < x) y)));

assert ⊢ arith_mult_neg m (APP (APP < x) y)
         : Proof (APP (APP => (APP (APP and (APP (APP < m) (of_Z 0)))
                              (APP (APP and (APP (APP < x) y)) true)))
                 ({|$mk_arith_mult_neg|} m (APP (APP < x) y)));

// ============================================================
// Proof rules: arith_trichotomy
// ============================================================

// From ¬(x < y) and ¬(x = y), conclude (x > y)  [after normalization]
assert ⊢ arith_trichotomy
         : Proof (APP (APP < x) y)
           → Proof (APP (APP (@= Int) x) y)
           → Proof ({|$mk_arith_trichotomy|}
                    ({|$arith_normalize_lit|} (APP not (APP (APP < x) y)))
                    ({|$arith_normalize_lit|} (APP not (APP (APP (@= Int) x) y))));
