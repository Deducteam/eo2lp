require open cpc.rules.Rewrites;

symbol x : τ Int;
symbol y : τ Int;
symbol z : τ Int;
symbol p : τ Bool;
symbol q : τ Bool;
symbol r : τ Bool;
symbol a : τ (Array Int Int);
symbol e : τ Int;
symbol s : τ ({|eo::Set|} Int);
symbol t : τ ({|eo::Set|} Int);

// ============================================================
// Arithmetic rewrites
// ============================================================

// div_total by 1
assert ⊢ {|arith-int-div-total-one|} x
         : Proof (APP (APP = (APP (APP div_total (of_Z 1)) x)) x);

// div_total by 0
assert ⊢ {|arith-int-div-total-zero|} x
         : Proof (APP (APP = (APP (APP div_total (of_Z 0)) x)) (of_Z 0));

// mod_total by 1
assert ⊢ {|arith-int-mod-total-one|} x
         : Proof (APP (APP = (APP (APP mod_total x) (of_Z 1))) (of_Z 0));

// mod_total by 0
assert ⊢ {|arith-int-mod-total-zero|} x
         : Proof (APP (APP = (APP (APP mod_total x) (of_Z 0))) x);

// > elimination
assert ⊢ {|arith-elim-gt|} x y
         : Proof (APP (APP = (APP (APP > x) y)) (APP not (APP (APP >= y) x)));

// < elimination
assert ⊢ {|arith-elim-lt|} x y
         : Proof (APP (APP = (APP (APP < x) y)) (APP not (APP (APP >= x) y)));

// int > elimination
assert ⊢ {|arith-elim-int-gt|} x y
         : Proof (APP (APP = (APP (APP > x) y))
                 (APP (APP >= x) (APP (APP + y) (APP (APP + (of_Z 1)) (of_Z 0)))));

// int < elimination
assert ⊢ {|arith-elim-int-lt|} x y
         : Proof (APP (APP = (APP (APP < x) y))
                 (APP (APP >= y) (APP (APP + x) (APP (APP + (of_Z 1)) (of_Z 0)))));

// <= elimination
assert ⊢ {|arith-elim-leq|} x y
         : Proof (APP (APP = (APP (APP <= x) y)) (APP (APP >= y) x));

// <= normalization
assert ⊢ {|arith-leq-norm|} x y
         : Proof (APP (APP = (APP (APP <= x) y))
                 (APP not (APP (APP >= x) (APP (APP + y) (APP (APP + (of_Z 1)) (of_Z 0))))));

// >= tightening
assert ⊢ {|arith-geq-tighten|} x y
         : Proof (APP (APP = (APP not (APP (APP >= x) y)))
                 (APP (APP >= y) (APP (APP + x) (APP (APP + (of_Z 1)) (of_Z 0)))));

// >= normalization
assert ⊢ {|arith-geq-norm1-int|} x y
         : Proof (APP (APP = (APP (APP >= x) y)) (APP (APP >= (APP (APP {|-_1|} y) x)) (of_Z 0)));

// = elimination for integers
assert ⊢ {|arith-eq-elim-int|} x y
         : Proof (APP (APP = (APP (APP = x) y))
                 (APP (APP and (APP (APP >= x) y)) (APP (APP and (APP (APP <= x) y)) true)));

// min is less than both
assert ⊢ {|arith-min-lt1|} x y
         : Proof (APP (APP = (APP (APP <= (ite (APP (APP < x) y) x y)) x)) true);
assert ⊢ {|arith-min-lt2|} x y
         : Proof (APP (APP = (APP (APP <= (ite (APP (APP < x) y) x y)) y)) true);

// max is greater than both
assert ⊢ {|arith-max-geq1|} x y
         : Proof (APP (APP = (APP (APP >= (ite (APP (APP >= x) y) x y)) x)) true);
assert ⊢ {|arith-max-geq2|} x y
         : Proof (APP (APP = (APP (APP >= (ite (APP (APP >= x) y) x y)) y)) true);

// abs(x) = abs(y)
assert ⊢ {|arith-abs-eq|} x y
         : Proof (APP (APP = (APP (APP = (APP abs x)) (APP abs y)))
                 (APP (APP or (APP (APP = x) y)) (APP (APP or (APP (APP = x) (APP - y))) false)));

// ============================================================
// Array rewrites
// ============================================================

// Read over write same index
assert ⊢ {|array-read-over-write|} a x e
         : Proof (APP (APP = (select (store a x e) x)) e);

// Store overwrite
assert ⊢ {|array-store-overwrite|} a x e y
         : Proof (APP (APP = (store (store a x e) x y)) (store a x y));

// Store self
assert ⊢ {|array-store-self|} a x
         : Proof (APP (APP = (store a x (select a x))) a);

// Read over write split: args are (t1, i1, e1, j1)
// conclusion: select(store(t1, j1, e1), i1) = ite(i1=j1, e1, select(t1, i1))
assert ⊢ {|array-read-over-write-split|} a x e y
         : Proof (APP (APP = (select (store a y e) x)) (ite (APP (APP = x) y) e (select a x)));

// ============================================================
// Boolean rewrites
// ============================================================

// Double not elimination
assert ⊢ {|bool-double-not-elim|} p
         : Proof (APP (APP = (APP not (APP not p))) p);

// eq true / eq false
assert ⊢ {|bool-eq-true|} p
         : Proof (APP (APP = (APP (APP = p) true)) p);
assert ⊢ {|bool-eq-false|} p
         : Proof (APP (APP = (APP (APP = p) false)) (APP not p));

// eq non-reflexivity
assert ⊢ {|bool-eq-nrefl|} p
         : Proof (APP (APP = (APP (APP = p) (APP not p))) false);

// impl false/true
assert ⊢ {|bool-impl-false1|} p
         : Proof (APP (APP = (APP (APP => p) false)) (APP not p));
assert ⊢ {|bool-impl-false2|} p
         : Proof (APP (APP = (APP (APP => false) p)) true);
assert ⊢ {|bool-impl-true1|} p
         : Proof (APP (APP = (APP (APP => p) true)) true);
assert ⊢ {|bool-impl-true2|} p
         : Proof (APP (APP = (APP (APP => true) p)) p);

// impl elimination
assert ⊢ {|bool-impl-elim|} p q
         : Proof (APP (APP = (APP (APP => p) q))
                 (APP (APP or (APP not p)) (APP (APP or q) false)));

// xor rewrites
assert ⊢ {|bool-xor-refl|} p
         : Proof (APP (APP = (APP (APP xor p) p)) false);
assert ⊢ {|bool-xor-nrefl|} p
         : Proof (APP (APP = (APP (APP xor (APP not p)) p)) true);
assert ⊢ {|bool-xor-false|} p
         : Proof (APP (APP = (APP (APP xor false) p)) p);
assert ⊢ {|bool-xor-true|} p
         : Proof (APP (APP = (APP (APP xor true) p)) (APP not p));
assert ⊢ {|bool-xor-comm|} p q
         : Proof (APP (APP = (APP (APP xor q) p)) (APP (APP xor p) q));
assert ⊢ {|bool-xor-elim|} p q
         : Proof (APP (APP = (APP (APP xor q) p)) (APP (APP = (APP not p)) q));

// De Morgan laws
assert ⊢ {|bool-or-de-morgan|} p q (APP (APP or r) false)
         : Proof (APP (APP = (APP not (APP (APP or p) (APP (APP or q) (APP (APP or r) false)))))
                 (APP (APP and (APP not p))
                 (APP (APP and (APP not ({|eo::list_singleton_elim|} or (APP (APP or q) (APP (APP or r) false))))) true)));

assert ⊢ {|bool-implies-de-morgan|} p q
         : Proof (APP (APP = (APP not (APP (APP => p) q)))
                 (APP (APP and p) (APP (APP and (APP not q)) true)));

assert ⊢ {|bool-and-de-morgan|} p q (APP (APP and r) true)
         : Proof (APP (APP = (APP not (APP (APP and p) (APP (APP and q) (APP (APP and r) true)))))
                 (APP (APP or (APP not p))
                 (APP (APP or (APP not ({|eo::list_singleton_elim|} and (APP (APP and q) (APP (APP and r) true))))) false)));

// ============================================================
// ITE rewrites
// ============================================================

// ite true/false conditions
assert ⊢ {|ite-true-cond|} x y : Proof (APP (APP = (ite true x y)) x);
assert ⊢ {|ite-false-cond|} x y : Proof (APP (APP = (ite false x y)) y);

// ite not condition
assert ⊢ {|ite-not-cond|} p x y
         : Proof (APP (APP = (ite (APP not p) x y)) (ite p y x));

// ite equal branches
assert ⊢ {|ite-eq-branch|} p x : Proof (APP (APP = (ite p x x)) x);

// ite then/else with true/false
assert ⊢ {|ite-then-true|} p q
         : Proof (APP (APP = (ite p true q))
                 (APP (APP or p) (APP (APP or q) false)));
assert ⊢ {|ite-else-false|} p q
         : Proof (APP (APP = (ite p q false))
                 (APP (APP and p) (APP (APP and q) true)));
assert ⊢ {|ite-then-false|} p q
         : Proof (APP (APP = (ite p false q))
                 (APP (APP and (APP not p)) (APP (APP and q) true)));
assert ⊢ {|ite-else-true|} p q
         : Proof (APP (APP = (ite p q true))
                 (APP (APP or (APP not p)) (APP (APP or q) false)));

// ite expand
assert ⊢ {|ite-expand|} p q r
         : Proof (APP (APP = (ite p q r))
                 (APP (APP and (APP (APP or (APP not p)) (APP (APP or q) false)))
                 (APP (APP and (APP (APP or p) (APP (APP or r) false))) true)));

// not-ite elimination
assert ⊢ {|bool-not-ite-elim|} p q r
         : Proof (APP (APP = (APP not (ite p q r))) (ite p (APP not q) (APP not r)));

// ite lookahead
assert ⊢ {|ite-then-lookahead|} p x y z
         : Proof (APP (APP = (ite p (ite p x y) z)) (ite p x z));
assert ⊢ {|ite-else-lookahead|} p x y z
         : Proof (APP (APP = (ite p x (ite p y z))) (ite p x z));

// ite self-lookahead (boolean)
assert ⊢ {|ite-then-lookahead-self|} p q
         : Proof (APP (APP = (ite p p q)) (ite p true q));
assert ⊢ {|ite-else-lookahead-self|} p q
         : Proof (APP (APP = (ite p q p)) (ite p q false));

// ============================================================
// Equality rewrites
// ============================================================

// eq reflexivity
assert ⊢ {|eq-refl|} x : Proof (APP (APP = (APP (APP = x) x)) true);

// eq symmetry
assert ⊢ {|eq-symm|} x y
         : Proof (APP (APP = (APP (APP = x) y)) (APP (APP = y) x));

// eq ite lift
assert ⊢ {|eq-ite-lift|} p x y z
         : Proof (APP (APP = (APP (APP = (ite p x y)) z)) (ite p (APP (APP = x) z) (APP (APP = y) z)));

// distinct binary elimination
assert ⊢ {|distinct-binary-elim|} x y
         : Proof (APP (APP = (APP distinct ({|eo::List::cons|} x ({|eo::List::cons|} y {|eo::List::nil|})))) (APP not (APP (APP = x) y)));

// ============================================================
// Set rewrites
// ============================================================

// member of singleton
assert ⊢ {|sets-member-singleton|} x y
         : Proof (APP (APP = ({|set.member|} x ({|set.singleton|} y))) (APP (APP = x) y));

// subset elimination
assert ⊢ {|sets-subset-elim|} s t
         : Proof (APP (APP = ({|set.subset|} s t)) (APP (APP = ({|set.union|} s t)) t));

// union/inter commutativity
assert ⊢ {|sets-union-comm|} s t
         : Proof (APP (APP = ({|set.union|} s t)) ({|set.union|} t s));
assert ⊢ {|sets-inter-comm|} s t
         : Proof (APP (APP = ({|set.inter|} s t)) ({|set.inter|} t s));

// inter member
assert ⊢ {|sets-inter-member|} x s t
         : Proof (APP (APP = ({|set.member|} x ({|set.inter|} s t)))
                 (APP (APP and ({|set.member|} x s)) (APP (APP and ({|set.member|} x t)) true)));

// minus member
assert ⊢ {|sets-minus-member|} x s t
         : Proof (APP (APP = ({|set.member|} x ({|set.minus|} s t)))
                 (APP (APP and ({|set.member|} x s)) (APP (APP and (APP not ({|set.member|} x t))) true)));

// union member
assert ⊢ {|sets-union-member|} x s t
         : Proof (APP (APP = ({|set.member|} x ({|set.union|} s t)))
                 (APP (APP or ({|set.member|} x s)) (APP (APP or ({|set.member|} x t)) false)));

// choose of singleton
assert ⊢ {|sets-choose-singleton|} x
         : Proof (APP (APP = ({|set.choose|} ({|set.singleton|} x))) x);

// is_singleton elimination
assert ⊢ {|sets-is-singleton-elim|} s
         : Proof (APP (APP = ({|set.is_singleton|} s)) (APP (APP = s) ({|set.singleton|} ({|set.choose|} s))));
