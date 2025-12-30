require open eo2lp.Zdiv;

inductive ℚ : TYPE ≔
  | Frac : ℤ → ℤ → ℚ;

symbol ⫽ : ℤ → ℤ → ℚ;
notation ⫽ infix 5;

// Helper to divide by GCD and construct.
symbol reduce_frac : ℤ → ℤ → ℤ → ℚ;
rule reduce_frac $n $d $g ↪ Frac (Zdiv $n $g) (Zdiv $d $g);

//// Logic:
//// 1. Calculate GCD of absolute values.
//// 2. Handle sign of denominator (if d < 0, flip signs of n and d).
//rule $n ⫽ Z0 ↪ Frac Z0 Z0 // Undefined case, returning 0/0
//with $n ⫽ (Zpos $d) ↪
//  reduce_frac $n (Zpos $d) (zgcd $n (Zpos $d))
//with $n ⫽ (Zneg $d) ↪
//  reduce_frac (— $n) (Zpos $d) (zgcd (— $n) (Zpos $d));

//compute 1 ⫽ 2;

symbol rat : Set;
rule τ rat ↪ ℚ;
