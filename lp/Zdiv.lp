require open Stdlib.Z;

inductive DivRes : TYPE ≔
| MkDivRes : ℤ → ℤ → DivRes;

// is the current remainder candidate >= divisor?
symbol div_step_aux : Comp → ℤ → ℤ → ℙ → DivRes;
rule div_step_aux Lt $q $r _  ↪ MkDivRes (double $q) $r
with div_step_aux Eq $q _ _   ↪ MkDivRes (succ_double $q) Z0
with div_step_aux Gt $q $r $d ↪ MkDivRes (succ_double $q) ($r - Zpos $d);

// 3. Recursive steps for division on Positive integers (ℙ)
symbol div_step_O : DivRes → ℙ → DivRes;
symbol div_step_I : DivRes → ℙ → DivRes;

// Step for bit 0: candidate = 2 * remainder
rule div_step_O (MkDivRes $q $r) $d ↪
  div_step_aux (double $r ≐ Zpos $d) $q (double $r) $d;

// Step for bit 1: candidate = 2 * remainder + 1
rule div_step_I (MkDivRes $q $r) $d ↪
  div_step_aux (succ_double $r ≐ Zpos $d) $q (succ_double $r) $d;

symbol div_rem_pos_1 : ℙ → DivRes;
rule div_rem_pos_1 H ↪ MkDivRes _1 Z0         // 1 / 1 = 1 rem 0
with div_rem_pos_1 _ ↪ MkDivRes Z0 _1;         // 1 / d = 0 rem 1 (for d > 1)

symbol div_rem_pos : ℙ → ℙ → DivRes;
rule div_rem_pos H $d ↪ div_rem_pos_1 $d
with div_rem_pos (O $a) $d ↪ div_step_O (div_rem_pos $a $d) $d
with div_rem_pos (I $a) $d ↪ div_step_I (div_rem_pos $a $d) $d;

// 4. Extractors and Sign Logic for zdiv
symbol zdiv_get_pos : DivRes → ℤ;
symbol zdiv_get_neg : DivRes → ℤ;

rule zdiv_get_pos (MkDivRes $q _) ↪ $q;

rule zdiv_get_neg (MkDivRes $q Z0) ↪ — $q
with zdiv_get_neg (MkDivRes $q (Zpos _)) ↪ — ($q + _1)
with zdiv_get_neg (MkDivRes $q (Zneg _)) ↪ — ($q + _1);

// 5. The zdiv symbol
symbol Zdiv : ℤ → ℤ → ℤ;
rule Zdiv Z0 _ ↪ Z0
with Zdiv (Zpos $a) (Zpos $b) ↪ zdiv_get_pos (div_rem_pos $a $b)
with Zdiv (Zneg $a) (Zneg $b) ↪ zdiv_get_pos (div_rem_pos $a $b)
with Zdiv (Zpos $a) (Zneg $b) ↪ zdiv_get_neg (div_rem_pos $a $b)
with Zdiv (Zneg $a) (Zpos $b) ↪ zdiv_get_neg (div_rem_pos $a $b);



// -------- implementing zmod --------
// Case: +a / +b. Result is just r.
symbol zmod_get_pos_pos : DivRes → ℤ;
rule zmod_get_pos_pos (MkDivRes _ $r) ↪ $r;

// Case: -a / -b. Result is -r.
symbol zmod_get_neg_neg : DivRes → ℤ;
rule zmod_get_neg_neg (MkDivRes _ Z0) ↪ Z0
with zmod_get_neg_neg (MkDivRes _ (Zpos $r)) ↪ Zneg $r;

// Case: +a / -b.
// If r=0, result is 0.
// If r>0, result is r - b (since b is negative, this is r - |b|).
symbol zmod_get_pos_neg : DivRes → ℙ → ℤ;
rule zmod_get_pos_neg (MkDivRes _ Z0) _ ↪ Z0
with zmod_get_pos_neg (MkDivRes _ (Zpos $r)) $b ↪ sub $r $b;

// Case: -a / +b.
// If r=0, result is 0.
// If r>0, result is b - r (since b is positive).
symbol zmod_get_neg_pos : DivRes → ℙ → ℤ;
rule zmod_get_neg_pos (MkDivRes _ Z0) _ ↪ Z0
with zmod_get_neg_pos (MkDivRes _ (Zpos $r)) $b ↪ sub $b $r;


symbol zmod : ℤ → ℤ → ℤ;

rule zmod Z0 _ ↪ Z0
with zmod (Zpos $a) (Zpos $b) ↪ zmod_get_pos_pos (div_rem_pos $a $b)
with zmod (Zneg $a) (Zneg $b) ↪ zmod_get_neg_neg (div_rem_pos $a $b)
with zmod (Zpos $a) (Zneg $b) ↪ zmod_get_pos_neg (div_rem_pos $a $b) $b
with zmod (Zneg $a) (Zpos $b) ↪ zmod_get_neg_pos (div_rem_pos $a $b) $b;

symbol % ≔ zmod;
notation % infix 5;



compute 9 + 2;

compute 9 % 3;
