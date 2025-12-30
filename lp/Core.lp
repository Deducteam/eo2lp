require open Stdlib.HOL Stdlib.Bool Stdlib.Z Stdlib.String;
require open Stdlib.List;
require open eo2lp.Q;

// object-level application.
constant symbol ▫ [a b]
  : τ (a ⤳ b) → τ a → τ b;
notation ▫ infix left 5;

injective symbol eo : Set → TYPE;

symbol Type : Set;
rule eo Type ↪ Set;


symbol halt [a] : eo a;
//If t is ground, this returns true if t is a value, and false otherwise. If t is not ground, it does not evaluate.
sequential symbol is_okay
 [t] : eo t → eo bool;

constant symbol true : eo bool;
constant symbol false : eo bool;
rule eo bool ↪ 𝔹;

rule eo string ↪ String;


rule eo ($x ⤳ $y) ↪ eo $x → eo $y;

symbol ifset : 𝔹 → Set → Set → Set;
rule ifset true $x _ ↪ $x
with ifset false _ $y ↪ $y;

sequential symbol ite
  [x y ] (p : eo bool) : eo (x ⤳ y ⤳ ifset p x y);

rule ite  true $t1 _ ↪ $t1
with ite false _ $t2 ↪ $t2;

sequential symbol eq
  [x y] : eo (x ⤳ y ⤳ bool);

sequential symbol is_eq
  [x y] : eo (x ⤳ y ⤳ bool);

sequential symbol cond
  [x] : eo (bool ⤳ x ⤳ x);
rule cond true $t ↪ $t;

sequential symbol requires
  [x y z] : eo (x ⤳ y ⤳ z ⤳ z);
rule requires $t1 $t2 $t3
  ↪ cond (is_eq $t1 $t2) $t3;

sequential symbol hash
  [x] : eo x → ℤ;

sequential symbol typeof
  [x] : eo x → eo Type;
rule typeof [$x] $t ↪ $x;

sequential symbol nameof
  [x] : eo x → eo string;

sequential symbol var
  (_ : eo string) (t : eo Type) : eo t;

rule nameof (var $s _) ↪ $s;
rule typeof (var _ $t) ↪ $t;

sequential symbol cmp
  [x y] : eo (x ⤳ y ⤳ bool);

sequential symbol is_z
  [x] : eo (x ⤳ bool);

sequential symbol is_q
  [x] : eo (x ⤳ bool);

sequential symbol is_bin
  [x] : eo (x ⤳ bool);

sequential symbol is_str
  [x] : eo (x ⤳ bool);

sequential symbol is_bool
  [x] : eo (x ⤳ bool);

sequential symbol is_var
  [x] : eo (x ⤳ bool);


// ---- boolean operators ----
symbol and [x] : eo (x ⤳ x ⤳ x);

rule and true true ↪ true
with and false _ ↪ false
with and _ false ↪ false;

symbol or [x] : eo (x ⤳ x ⤳ x);

rule or false false ↪ false
with or true _ ↪ true
with and _ true ↪ true;

symbol xor [x] : eo (x ⤳ x ⤳ x);

rule xor true false ↪ true
with xor false true ↪ true
with xor false false ↪ false
with xor false false ↪ false;

symbol not [x] : eo (x ⤳ x);

rule not true ↪ false
with not false ↪ true;


// --- arithmetic ---
rule eo int ↪ ℤ;

symbol neg [x] : eo (x ⤳ x);
rule neg [int] $x ↪ — $x;

symbol add [x] : eo (x ⤳ x ⤳ x);
rule add [int] $x $y ↪ $x + $y;

symbol mul [x] : eo (x ⤳ x ⤳ x);
rule mul [int] $x $y ↪ $x * $y;

symbol qdiv [x] : eo (x ⤳ x ⤳ x);
symbol zdiv [x] : eo (x ⤳ x ⤳ x);

symbol zmod [x] : eo (x ⤳ x ⤳ x);

symbol is_neg [x] : eo (x ⤳ bool);
symbol gt [x] : eo (x ⤳ x ⤳ bool);

// --- strings ---
symbol len [x] : eo (x ⤳ int);
symbol concat [x] : eo (x ⤳ x ⤳ bool);
symbol extract [x] : eo (x ⤳ int ⤳ int ⤳ x);
symbol find : eo (string ⤳ string ⤳ int);

// --- conversion ----
symbol to_z [x] : eo (x ⤳ int);
symbol to_q [x] : eo (x ⤳ rat);
symbol to_bin [x] : eo (x ⤳ pos);
symbol to_str [x] : eo (x ⤳ string);

// ---- list ops ----
symbol nil [x y] (f : eo (x ⤳ y ⤳ y))
  (t : eo Type) : eo t;

symbol cons [x y] (f : eo (x ⤳ y ⤳ y))
  (t1 : eo x) (t2 : eo y) : eo y
  ≔ f t1 t2;

symbol list_len [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ int);

symbol list_concat [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ y ⤳ y);

symbol list_nth [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ int ⤳ x);

symbol list_find [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ x ⤳ int);

symbol list_rev [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ y);

symbol list_erase [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ y);

symbol list_erase_all [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ y);

symbol list_setof [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ y);

symbol list_minclude [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ y ⤳ bool);

symbol list_meq [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ y ⤳ y);

symbol list_diff [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ y);

symbol list_singleton_elim [x y] (f : eo (x ⤳ y ⤳ y))
  : eo (y ⤳ x);
