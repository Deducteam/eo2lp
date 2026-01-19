require open
  Stdlib.Set
  Stdlib.HOL
  Stdlib.List
  Stdlib.String
  Stdlib.Z
  Stdlib.Bool;

symbol ℚ : TYPE;

// the set of all Eunoia types.
symbol Type : Set;
rule τ Type ↪ Set;

// dependent arrow type for quoting
symbol ⤳d (T : τ Type) : τ (T ⤳ Type) → τ Type;
notation ⤳d infix right 5;
rule τ ($T ⤳d $F) ↪ (Π x : τ $T, τ ($F x));

// higher-order application.
symbol ⋅ [a b] : τ (a ⤳ b) → τ a → τ b;
notation ⋅ infix left 5;

// inlined typechecking.
symbol _as (a : Set) (x : τ a) : τ a;
rule _as _ $x ↪ $x;

// Core types - use Stdlib types where possible
symbol Bool : Set;
rule τ Bool ↪ 𝔹;
symbol Str : Set;
rule τ Str ↪ Stdlib.String.String;
symbol Z : Set;
rule τ Z ↪ ℤ;
symbol Q : Set;
rule τ Q ↪ ℚ;
symbol mkrat : ℤ → ℤ → ℚ;

symbol ?? : 𝔹 → Set → Set → Set;
rule ?? _ $x $x ↪ $x
with ?? true $x _ ↪ $x
with ?? false _ $y ↪ $y;

// just !arith_typeunion but for the eo.add, etc.
symbol ⊍ : Set → Set → Set; notation ⊍ infix 5;
rule Z ⊍ Z ↪ Z
with Q ⊍ Q ↪ Q
with Q ⊍ Z ↪ Q
with Z ⊍ Q ↪ Q;

// Eunoia builtins
sequential symbol is_ok [T : Set]: τ (T ⤳ Bool);
sequential symbol ite [U T : Set] (b : τ Bool) : τ (U ⤳ T ⤳ (?? b U T));
sequential symbol eq [T : Set] [S : Set] : τ (T ⤳ S ⤳ Bool);
sequential symbol is_eq [T : Set] [S : Set]: τ (T ⤳ S ⤳ Bool);
sequential symbol requires [T : Set] [U : Set] [V : Set]: τ (T ⤳ U ⤳ V ⤳ V);
sequential symbol hash [T : Set]: τ (T ⤳ Z);
sequential symbol typeof [T : Set]: τ (T ⤳ Type);
sequential symbol nameof [T : Set]: τ (T ⤳ Str);
sequential symbol var [T : Set]: τ (Str ⤳ T ⤳ T);
sequential symbol cmp [T : Set] [U : Set]: τ (T ⤳ U ⤳ Bool);
sequential symbol is_var [T : Set]: τ (T ⤳ Bool);
sequential symbol is_z [T : Set]: τ (T ⤳ Bool);
sequential symbol and : τ (Bool ⤳ Bool ⤳ Bool);
sequential symbol or : τ (Bool ⤳ Bool ⤳ Bool);
sequential symbol xor : τ (Bool ⤳ Bool ⤳ Bool);
sequential symbol not : τ (Bool ⤳ Bool);
sequential symbol add [T1 : Set] [T2 : Set] : τ (T1 ⤳ T2 ⤳ (T1 ⊍ T2));
sequential symbol mul [T1 : Set] [T2 : Set] : τ (T1 ⤳ T2 ⤳ (T1 ⊍ T2));
sequential symbol neg [T : Set]: τ (T ⤳ T);
sequential symbol qdiv [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol zdiv [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol zmod [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol is_neg [T : Set]: τ (T ⤳ Bool);
sequential symbol gt [T : Set] [U : Set]: τ (T ⤳ U ⤳ Bool);
sequential symbol len [T : Set]: τ (T ⤳ Z);
sequential symbol concat [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol extract [T : Set]: τ (T ⤳ Z ⤳ Z ⤳ T);
sequential symbol find : τ (Str ⤳ Str ⤳ Z);
sequential symbol to_z [T : Set]: τ (T ⤳ Z);
sequential symbol to_q [T : Set]: τ (T ⤳ Q);
sequential symbol to_bin [T : Set]: τ (Z ⤳ T ⤳ T);
sequential symbol to_str [T : Set]: τ (T ⤳ Str);
sequential symbol quote [T : Set]: τ (T ⤳ T);
sequential symbol nil [U : Set] [T : Set]: τ ((U ⤳ T ⤳ T) ⤳ Type ⤳ T);
sequential symbol cons [U : Set] [T : Set]: τ ((U ⤳ T ⤳ T) ⤳ U ⤳ T ⤳ T);
sequential symbol list_concat [U : Set] [T : Set]: τ ((U ⤳ T ⤳ T) ⤳ T ⤳ T ⤳ T);
sequential symbol list_len [F : Set] [T : Set]: τ (F ⤳ T ⤳ Z);
sequential symbol list_nth [F : Set] [T : Set]: τ (F ⤳ T ⤳ Z ⤳ T);
sequential symbol list_find [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ Z);
sequential symbol list_rev [F : Set] [T : Set]: τ (F ⤳ T ⤳ T);
sequential symbol list_erase [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ T);
sequential symbol list_erase_all [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ T);
sequential symbol list_setof [F : Set] [T : Set]: τ (F ⤳ T ⤳ T);
sequential symbol list_minclude [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ Bool);
sequential symbol list_meq [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ Bool);
sequential symbol list_diff [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ T);
sequential symbol list_inter [F : Set] [T : Set]: τ (F ⤳ T ⤳ T ⤳ T);
sequential symbol list_singleton_elim [F : Set] [T : Set]: τ (F ⤳ T ⤳ T);

// eo::List, eo::List::cons, eo::List::ni
symbol List : τ Type;
sequential symbol List__nil : τ List; symbol ∎ ≔ List__nil;
sequential symbol List__cons [T : Set]: τ (T ⤳ List ⤳ List);
