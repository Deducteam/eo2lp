//require open eo2lp.Core;
require open
  Stdlib.Set
  Stdlib.HOL
  Stdlib.List
  Stdlib.String
  Stdlib.Z
  Stdlib.Bool;
symbol ℚ : TYPE;

// for each `x : Set`, we have `τ x : TYPE`.
// for any eo-term `t`, we have `t : τ (eo::typeof t)`.

// the set of all Eunoia types.
symbol Type : Set;
rule τ Type ↪ Set;

// higher-order application.
symbol ∗ [a b] : τ (a ⤳ b) → τ a → τ b;
notation ∗ infix left 5;

// inlined typechecking.
symbol _as (a : Set) (x : τ a) : τ a;
rule _as $ty $x ↪ $x;

// translate `Core.eo`.
constant symbol Bool : Set;
constant symbol true : τ Bool;
constant symbol false : τ Bool;
constant symbol String : Set;
constant symbol Z : Set; rule τ Z ↪ ℤ;
constant symbol Q : Set; rule τ Q ↪ ℚ;

sequential symbol is_ok [T : Set]: τ (T ⤳ Bool);
sequential symbol ite [T : Set]: τ (Bool ⤳ T ⤳ T ⤳ T);
sequential symbol eq [U : Set]: τ (U ⤳ U ⤳ Bool);
sequential symbol is_eq [T : Set] [S : Set]: τ (T ⤳ S ⤳ Bool);
sequential symbol requires [T : Set] [U : Set] [V : Set]: τ (T ⤳ U ⤳ V ⤳ V);
sequential symbol hash [T : Set]: τ (T ⤳ Z);
sequential symbol typeof [T : Set]: τ (T ⤳ Type);
sequential symbol nameof [T : Set]: τ (T ⤳ String);
sequential symbol var [T : Set]: τ (String ⤳ T ⤳ T);
sequential symbol cmp [T : Set] [U : Set]: τ (T ⤳ U ⤳ Bool);
sequential symbol is_var [T : Set]: τ (T ⤳ Bool);
sequential symbol and : τ (Bool ⤳ Bool ⤳ Bool);
sequential symbol or : τ (Bool ⤳ Bool ⤳ Bool);
sequential symbol xor : τ (Bool ⤳ Bool ⤳ Bool);
sequential symbol not : τ (Bool ⤳ Bool);
sequential symbol add [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol mul [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol neg [T : Set]: τ (T ⤳ T);
sequential symbol qdiv [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol zdiv [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol zmod [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol is_neg [T : Set]: τ (T ⤳ Bool);
sequential symbol gt [T : Set] [U : Set]: τ (T ⤳ U ⤳ Bool);
sequential symbol len [T : Set]: τ (T ⤳ Z);
sequential symbol concat [T : Set]: τ (T ⤳ T ⤳ T);
sequential symbol extract [T : Set]: τ (T ⤳ Z ⤳ Z ⤳ T);
sequential symbol find : τ (String ⤳ String ⤳ Z);
sequential symbol to_z [T : Set]: τ (T ⤳ Z);
sequential symbol to_q [T : Set]: τ (T ⤳ Q);
sequential symbol to_bin [T : Set]: τ (Z ⤳ T ⤳ T);
sequential symbol to_str [T : Set]: τ (T ⤳ String);
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
sequential symbol List : Set;
sequential symbol List__nil : τ List;
sequential symbol List__cons [T : Set]: τ (T ⤳ List ⤳ List);

//symbol _and [a] : τ a;
