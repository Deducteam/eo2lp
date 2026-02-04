require open cpc.Cpc;

// $run_evaluate: arithmetic
assert ⊢ {|$run_evaluate|} (APP (APP + (of_Z 2)) (of_Z 3)) ≡ of_Z 5;
assert ⊢ {|$run_evaluate|} (APP - (of_Z 7)) ≡ of_Z -7;
assert ⊢ {|$run_evaluate|} (APP (APP * (of_Z 3)) (of_Z 4)) ≡ of_Z 12;

// $run_evaluate: boolean
assert ⊢ {|$run_evaluate|} (APP not true) ≡ false;
assert ⊢ {|$run_evaluate|} (APP not false) ≡ true;
assert ⊢ {|$run_evaluate|} (APP (APP or true) false) ≡ true;
assert ⊢ {|$run_evaluate|} (APP (APP or false) false) ≡ false;
assert ⊢ {|$run_evaluate|} (APP (APP and true) false) ≡ false;
assert ⊢ {|$run_evaluate|} (APP (APP and true) true) ≡ true;

// $run_evaluate: comparison
assert ⊢ {|$run_evaluate|} (APP (APP < (of_Z 1)) (of_Z 2)) ≡ true;
assert ⊢ {|$run_evaluate|} (APP (APP < (of_Z 2)) (of_Z 1)) ≡ false;
assert ⊢ {|$run_evaluate|} (APP (APP > (of_Z 5)) (of_Z 3)) ≡ true;

// $run_evaluate: equality
assert ⊢ {|$run_evaluate|} (APP (APP (@= Int) (of_Z 1)) (of_Z 1)) ≡ true;
assert ⊢ {|$run_evaluate|} (APP (APP (@= Int) (of_Z 1)) (of_Z 2)) ≡ false;
assert ⊢ {|$run_evaluate|} (APP (APP (@= Bool) true) true) ≡ true;
assert ⊢ {|$run_evaluate|} (APP (APP (@= Bool) true) false) ≡ false;

// $run_evaluate: identity fallthrough
assert ⊢ {|$run_evaluate|} (of_Z 42) ≡ of_Z 42;
assert ⊢ {|$run_evaluate|} true ≡ true;

// Proof rules are available
assert ⊢ refl (of_Z 0) : Proof (APP (APP = (of_Z 0)) (of_Z 0));
