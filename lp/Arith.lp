require open eo2lp.Zdiv eo2lp.Q Stdlib.HOL;

symbol If : 𝔹 → Set → Set → Set;
rule If true $a _  ↪ $a
with If false _ $b ↪ $b;

sequential symbol {|eo::ite|}
  [a b] (p : 𝔹) : τ (a ⤳ b ⤳ If p a b);
rule {|eo::ite|} true $x _ ↪ $x
with {|eo::ite|} false _ $y ↪ $y;

sequential symbol {|eo::is_neg|}
  [a] : τ (a ⤳ bool);

sequential symbol {|eo::neg|}
  [a] : τ (a ⤳ a);

sequential symbol {|eo::add|}
  [a : Set] : τ (a ⤳ a ⤳ a);

sequential symbol {|eo::zdiv|}
  [a : Set] : τ (a ⤳ a ⤳ a);

sequential symbol {|eo::to_q|}
  [a b : Set] : τ (a ⤳ b);

sequential symbol {|eo::is_eq_type|}
  : Set → Set → 𝔹;

rule {|eo::is_eq_type|} $x $x ↪ true
with {|eo::is_eq_type|} _ _   ↪ false;

sequential symbol {|eo::requires_type_in|}
  [U : Set] : Set → Set → τ U → τ U;

rule {|eo::requires_type_in|} $T $T $x ↪ $x;

constant symbol Int : Set;
constant symbol Z : ℤ → τ Int;

rule {|eo::add|} (Z $x) (Z $y) ↪ Z ($x + $y);
rule {|eo::is_neg|} (Z $x) ↪ isZneg $x;
rule {|eo::neg|} (Z $x) ↪ (Z (— $x));
rule {|eo::zdiv|} (Z $x) (Z $y) ↪ Z (zdiv $x $y);


sequential symbol log2 : τ (Int ⤳ Int);
rule log2 (Z 1) ↪ (Z 0)
with log2 $x ↪
  {|eo::add|} (Z 1) (log2 ({|eo::zdiv|} $x (Z 2)));

symbol sgn [T] (x : τ T) ≔
  {|eo::ite|} ({|eo::is_neg|} x)
    (Z -1)
    ({|eo::ite|} ({|eo::is_neg|} ({|eo::neg|} x))
      (Z 1) (Z 0));


constant symbol Real : Set;
constant symbol Q : ℚ → τ Real;

rule {|eo::to_q|} [Real] [Real] (Q $x) ↪ (Q $x)
with {|eo::to_q|} [Int] [Real]  (Z $x) ↪ (Q ($x ⫽ 1));

type Q (0 ⫽ 1);

symbol mk_zero (T : Set) ≔
  {|eo::ite|} ({|eo::is_eq_type|} T Int)
    (Z 0)
    ({|eo::requires_type_in|} T Real (Q (0 ⫽ 1)));

compute mk_zero Real;
