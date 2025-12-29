require open Logic.U.Arrow eo2lp.Core;
constant symbol Bool : Set;
constant symbol true : El Bool;
constant symbol false : El Bool;
constant symbol {|eo::requires|} [T : Set] [U : Set] : El (T ⤳ T ⤳ U ⤳ U);
constant symbol {|eo::typeof|} [T : Set] : (El T) → Set;
constant symbol {|eo::eq|} [U : Set] : El (U ⤳ U ⤳ Bool);
constant symbol {|eo::ite|} [T : Set] : El (Bool ⤳ T ⤳ T ⤳ T);
constant symbol {|eo::cmp|} [T : Set] [U : Set] : El (T ⤳ U ⤳ Bool);
constant symbol {|eo::is_var|} [T : Set] : El (T ⤳ Bool);
constant symbol {|eo::nil|} [U : Set] [T : Set] : (El (U ⤳ T ⤳ T)) → Set → (El T);
constant symbol {|eo::cons|} [U : Set] [T : Set] : El ((U ⤳ T ⤳ T) ⤳ U ⤳ T ⤳ T);
constant symbol {|eo::list_concat|} [U : Set] [T : Set] : El ((U ⤳ T ⤳ T) ⤳ T ⤳ T ⤳ T);
constant symbol {|eo::List|} : Set;
constant symbol {|eo::List::nil|} : El {|eo::List|};
constant symbol {|eo::List::cons|} [T : Set] : El (T ⤳ {|eo::List|} ⤳ {|eo::List|});
constant symbol {|@@Pair|} : Set → Set → Set;
constant symbol {|@@pair|} [U : Set] [T : Set] : El (U ⤳ T ⤳ ({|@@Pair|} U T));
sequential symbol {|$pair_first|} [T : Set] [S : Set] : El (({|@@Pair|} T S) ⤳ T);
rule {|$pair_first|} [$T] [$S] ({|@@pair|} [$T] [$S] ▫ $t ▫ $s) ↪ $t;
sequential symbol {|$pair_second|} [T : Set] [S : Set] : El (({|@@Pair|} T S) ⤳ S);
rule {|$pair_second|} [$T] [$S] ({|@@pair|} [$T] [$S] ▫ $t ▫ $s) ↪ $s;
sequential symbol {|$evaluate_list|} : El ({|eo::List|} ⤳ {|eo::List|});
sequential symbol {|$evaluate_internal|} [T : Set] : El (T ⤳ {|eo::List|} ⤳ T);
rule {|$evaluate_internal|} [$T] $t ({|eo::List::cons|} [$T] ▫ $tev ▫ {|eo::List::nil|}) ↪ $tev;
sequential symbol {|$get_arg_list_rec|} [S : Set] : El (S ⤳ {|eo::List|} ⤳ {|eo::List|});
rule {|$get_arg_list_rec|} [$S] ($f ▫ $x) $acc ↪ {|$get_arg_list_rec|} $f ({|eo::cons|} {|eo::List::cons|} $x $acc)
with {|$get_arg_list_rec|} [$S] $y $acc ↪ $acc;
sequential symbol {|$is_app|} [T : Set] [U : Set] [V : Set] : El ((T ⤳ U) ⤳ V ⤳ Bool);
rule {|$is_app|} [$T] [$U] [$U] $f ($f ▫ $x) ↪ true
with {|$is_app|} [$T] [$U] [$V] $f ($g ▫ $x) ↪ {|$is_app|} $f $g
with {|$is_app|} [$T] [$U] [$V] $f $t ↪ false;
sequential symbol {|$is_var_list|} : El ({|eo::List|} ⤳ Bool);
rule {|$is_var_list|} ({|eo::List::cons|} [$U] ▫ $x ▫ $xs) ↪ {|eo::ite|} ({|eo::is_var|} $x) ({|$is_var_list|} $xs) false
with {|$is_var_list|} {|eo::List::nil|} ↪ true;
constant symbol {|@@result.null|} : El Bool;
constant symbol {|@@result.invalid|} : El Bool;
sequential symbol {|$result_combine|} : El (Bool ⤳ Bool ⤳ Bool);
rule {|$result_combine|} $b1 {|@@result.null|} ↪ $b1
with {|$result_combine|} $b1 $b1 ↪ $b1
with {|$result_combine|} $b1 $b2 ↪ {|@@result.invalid|};
sequential symbol {|$assoc_nil_has_type_rec|} [T : Set] [U : Set] : (El (T ⤳ U ⤳ U)) → (El U) → Set → (El Bool);
rule {|$assoc_nil_has_type_rec|} [$T] [$U] $f ($f ▫ $x1 ▫ $x2) $W ↪ {|eo::requires_type_in|} ({|eo::typeof|} $x1) $W ({|$assoc_nil_has_type_rec|} $f $x2 $W)
with {|$assoc_nil_has_type_rec|} [$T] [$U] $f $nil $W ↪ true;
sequential symbol {|$assoc_nil_same_type|} [T : Set] [U : Set] : El ((T ⤳ U ⤳ U) ⤳ U ⤳ Bool);
rule {|$assoc_nil_same_type|} [$T] [$U] $f ($f ▫ $x1 ▫ $x2) ↪ {|$assoc_nil_has_type_rec|} $f $x2 ({|eo::typeof|} $x1);
constant symbol ite [A : Set] : El (Bool ⤳ A ⤳ A ⤳ A);
constant symbol not : El (Bool ⤳ Bool);
constant symbol or : El (Bool ⤳ Bool ⤳ Bool);
constant symbol and : El (Bool ⤳ Bool ⤳ Bool);
constant symbol => : El (Bool ⤳ Bool ⤳ Bool);
constant symbol xor : El (Bool ⤳ Bool ⤳ Bool);
constant symbol = [A : Set] : El (A ⤳ A ⤳ Bool);
sequential symbol {|$get_lambda_type|} : (El {|eo::List|}) → Set → Set;
rule {|$get_lambda_type|} ({|eo::List::cons|} [{|eo::List|}] ▫ $x ▫ $xs) $B ↪ ({|eo::typeof|} $x) ⤳ ({|$get_lambda_type|} $xs $B)
with {|$get_lambda_type|} {|eo::List::nil|} $B ↪ $B;
constant symbol lambda [B : Set] (L : El {|eo::List|}) : El (B ⤳ ({|$get_lambda_type|} L B));
constant symbol distinct [x0 : Set] (xs : El {|eo::List|}) : El ({|eo::requires_type_out|} [Bool] ({|$assoc_nil_same_type|} [x0] [{|eo::List|}] ({|eo::List::cons|} [x0]) xs) true Bool);
constant symbol {|@purify|} [A : Set] (t : El A) : El A;
