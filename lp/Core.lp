require open Stdlib.HOL Stdlib.Bool Stdlib.Z eo2lp.Q Stdlib.String;

symbol int ≔ int;
symbol rat ≔ rat;
symbol str ≔ string;

require open Stdlib.List;

// object-level application.
injective symbol app [a b]
  : τ (a ⤳ b) → τ a → τ b;

// --- fold right with nil terminator ---
symbol foldr_nil [a acc]
  : τ (a ⤳ acc ⤳ acc) → τ (list a) → τ acc → τ acc;

rule foldr_nil $f □ $y ↪ $y
with foldr_nil $f ($x ⸬ $xs) $y
   ↪ $f $x (foldr_nil $f $xs $y);

// --- fold left with nil terminator ---
symbol foldl_nil [a acc]
  : τ (acc ⤳ a ⤳ acc) → τ acc → τ (list a) → τ acc;

rule foldl_nil $f $y □ ↪ $y
with foldl_nil $f $y ($x ⸬ $xs)
   ↪ foldl_nil $f ($f $y $x) $xs;

// --- fold right. undefined for □! ---
symbol foldr [a]
  : τ (a ⤳ a ⤳ a) → τ (list a) → τ a;
rule foldr $f ($x ⸬ $xs) ↪
  foldr_nil $f (belast $x $xs) (last $x $xs);

// --- fold left. undefined for □! ---
symbol foldl [a]
  : τ (a ⤳ a ⤳ a) → τ (list a) → τ a;
rule foldl $f ($x ⸬ $xs) ↪
  foldl_nil $f (last $x $xs) (belast $x $xs);

(a : Set) inductive CONST_ATTR : TYPE ≔
  | RightAssocNil : τ a → CONST_ATTR a
  | LeftAssocNil : τ a → CONST_ATTR a
  | RightAssocNilNSN : τ a → CONST_ATTR a
  | LeftAssocNilNSN : τ a → CONST_ATTR a
  | LeftAssoc : CONST_ATTR a
  | RightAssoc : CONST_ATTR a
  | ArgList : τ a → CONST_ATTR a
  | Chainable : τ a → CONST_ATTR a
  | Pairwise : τ a → CONST_ATTR a
  | Binder : τ a → CONST_ATTR a;

// -- generic fold. dispatch on const attribute ---
// doesn't work because of types.
// so we do desugaring in OCaml still.
symbol fold [a b c d]
  : τ (a ⤳ b ⤳ c) → τ (list d) → CONST_ATTR c → τ c;
// it would work if we have a 'meta' file that just operates
// on eos. then, we use these meta rules to rewrite things.



rule fold $f $xs (RightAssocNil $t) ↪ foldr_nil $f $xs $t;
rule fold [$a] [$b] $f $xs (LeftAssocNil $t) ↪ foldl_nil $f $t $xs;

rule fold $f $xs LeftAssoc ↪ foldl $f $xs;

symbol ite [a] : 𝔹 → τ a → τ a → τ a;

symbol Type : Set;
rule τ Type ↪ Set;

symbol List : Set;
symbol List⋅⋅nil : τ List;
symbol List⋅⋅cons [a] : τ a → τ List → τ List;


// If t is ground, return true if t is a value,
// and false otherwise. If t is not ground, it does not evaluate.
sequential symbol is_okay
 [t] : τ t → τ bool;

rule τ bool ↪ 𝔹;
rule τ string ↪ String;


symbol ite [x] : τ (bool ⤳ x ⤳ x ⤳ x);
rule ite true $t1 _  ↪ $t1
with ite false _ $t2 ↪ $t2;

sequential symbol eq
  [x y] : τ (x ⤳ y ⤳ bool);

sequential symbol is_eq
  [x y] : τ (x ⤳ y ⤳ bool);

sequential symbol cond
  [x] : τ (bool ⤳ x ⤳ x);

rule cond true $t ↪ $t;

// ---- eo::requires ----
sequential symbol requires
  [x y z] : τ (x ⤳ y ⤳ z ⤳ z);
rule requires $t1 $t2 $t3
  ↪ cond (is_eq $t1 $t2) $t3;

symbol requires_type_in
  [x] : Set → Set → τ x → τ x;

symbol requires_type_out
  [x] : τ x → τ x → Set → Set;

sequential symbol hash
  [x] : τ x → ℤ;

sequential symbol typeof
  [x] : τ (x ⤳ Type);
//rule typeof [$x] $t ↪ $x;constant

sequential symbol nameof
  [x] : τ x → τ string;

//sequential symbol var
  //(_ : τ string) (t : τ Type) : τ t;

//rule nameof (var $s _) ↪ $s;
//rule typeof (var _ $t) ↪ $t;

sequential symbol cmp
  [x y] : τ (x ⤳ y ⤳ bool);

sequential symbol is_z
  [x] : τ (x ⤳ bool);

sequential symbol is_q
  [x] : τ (x ⤳ bool);

sequential symbol is_bin
  [x] : τ (x ⤳ bool);

sequential symbol is_str
  [x] : τ (x ⤳ bool);

sequential symbol is_bool
  [x] : τ (x ⤳ bool);

sequential symbol is_var
  [x] : τ (x ⤳ bool);


// ---- boolean operators ----
symbol and [x] : τ (x ⤳ x ⤳ x);

rule and true true ↪ true
with and false _ ↪ false
with and _ false ↪ false;

symbol or [x] : τ (x ⤳ x ⤳ x);

rule or false false ↪ false
with or true _ ↪ true
with and _ true ↪ true;

symbol xor [x] : τ (x ⤳ x ⤳ x);

rule xor true false ↪ true
with xor false true ↪ true
with xor false false ↪ false
with xor false false ↪ false;

symbol not [x] : τ (x ⤳ x);

rule not true ↪ false
with not false ↪ true;


// --- arithmetic ---
//rule τ int ↪ ℤ;

symbol neg [x] : τ (x ⤳ x);
rule neg [int] $x ↪ — $x;

symbol add [x] : τ (x ⤳ x ⤳ x);
rule add [int] $x $y ↪ $x + $y;

symbol mul [x] : τ (x ⤳ x ⤳ x);
rule mul [int] $x $y ↪ $x * $y;

symbol qdiv [x] : τ (x ⤳ x ⤳ x);
symbol zdiv [x] : τ (x ⤳ x ⤳ x);

symbol zmod [x] : τ (x ⤳ x ⤳ x);

symbol is_neg [x] : τ (x ⤳ bool);
symbol gt [x] : τ (x ⤳ x ⤳ bool);

// --- strings ---
symbol len [x] : τ (x ⤳ int);
symbol concat [x] : τ (x ⤳ x ⤳ bool);
symbol extract [x] : τ (x ⤳ int ⤳ int ⤳ x);
symbol find : τ (string ⤳ string ⤳ int);

// --- conversion ----
symbol to_z [x] : τ (x ⤳ int);
symbol to_q [x] : τ (x ⤳ rat);
symbol to_bin [x] : τ (x ⤳ pos);
symbol to_str [x] : τ (x ⤳ string);

// ---- list ops ----
symbol nil [x y] (f : τ (x ⤳ y ⤳ y))
  (t : τ Type) : τ y;

symbol cons [x y] (f : τ (x ⤳ y ⤳ y))
  (t1 : τ x) (t2 : τ y) : τ y
  ≔ f t1 t2;

symbol list_len [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ int);

symbol list_concat [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ y ⤳ y);

symbol list_nth [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ int ⤳ x);

symbol list_find [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ x ⤳ int);

symbol list_rev [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ y);

symbol list_erase [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ y);

symbol list_erase_all [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ y);

symbol list_setof [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ y);

symbol list_minclude [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ y ⤳ bool);

symbol list_meq [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ y ⤳ y);

symbol list_diff [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ y);

symbol list_singleton_elim [x y] (f : τ (x ⤳ y ⤳ y))
  : τ (y ⤳ x);
