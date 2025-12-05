require open Logic.U.Set Logic.U.Arrow;
require open eo2lp.Core;
constant symbol {|@@Pair|} : Set → Set → Set;
symbol {|@Pair|} ≔ {|@@Pair|};
constant symbol {|@@pair|} [U : Set] [T : Set]
  : El U → El T → El ({|@Pair|} U T);

symbol {|@pair|} [U] [T] ≔ {|@@pair|} [U] [T];

//symbol {|eo::as|} (α : Set) : El α → El α;
//symbol {|@pair|} [U] [T] ≔ {|eo::as|} (U ⤳ T ⤳ {|@Pair|} U T) {|@@pair|};


symbol force (a : Set) : El a → El a;

sequential symbol {|$pair_first|} [T : Set] [S : Set] : El ({|@Pair|} T S) → El T;
rule {|$pair_first|} ({|@pair|} $t $s) ↪ $t;



sequential symbol {|$pair_second|} [T : Set] [S : Set] : El ({|@Pair|} T S) → El S;
rule {|$pair_second|} ({|@pair|} $t $s) ↪ $s;
symbol {|@List|} ≔ {|eo::List|};
symbol {|@list.nil|} ≔ {|eo::List::nil|};
symbol {|@list|} ≔ {|eo::List::cons|};
sequential symbol {|$evaluate_list|} : El {|@List|} → El {|@List|};
sequential symbol {|$evaluate_internal|} [T : Set] : El T → El {|@List|} → El T;
rule {|$evaluate_internal|} $t ({|@list|} $tev) ↪ $tev;
symbol {|$evaluate|} [T : Set] (t : El T) ≔ {|$evaluate_internal|} t ({|$evaluate_list|} ({|@list|} t));
sequential symbol {|$get_arg_list_rec|} [S : Set] : El S → El {|@List|} → El {|@List|};
rule {|$get_arg_list_rec|} ($f ▫ $x) $acc ↪ {|$get_arg_list_rec|} $f ({|eo::cons|} {|@list|} $x $acc)
with {|$get_arg_list_rec|} $y $acc ↪ $acc;
symbol {|$get_arg_list|} [T : Set] (t : El T) ≔ {|$get_arg_list_rec|} t {|@list.nil|};
sequential symbol {|$is_app|} [T : Set] [S : Set] [U : Set] : (El T → El U) → El S → El Bool;
rule {|$is_app|} $f ($g ▫ $x) ↪ {|$is_app|} $f $g
with {|$is_app|} $f $x ↪ {|eo::eq|} $f $x;
sequential symbol {|$is_var_list|} : El {|@List|} → El Bool;
rule {|$is_var_list|} ({|@list|} $x $xs) ↪ {|eo::ite|} ({|eo::is_var|} $x) ({|$is_var_list|} $xs) false
with {|$is_var_list|} {|@list.nil|} ↪ true;
symbol {|$compare_var|} [T : Set] [U : Set] (a : El T) (b : El U) ≔ {|eo::cmp|} b a;
constant symbol {|@@result.null|} : El Bool;
symbol {|@result.null|} ≔ {|@@result.null|};
constant symbol {|@@result.invalid|} : El Bool;
symbol {|@result.invalid|} ≔ {|@@result.invalid|};
sequential symbol {|$result_combine|} : El Bool → El Bool → El Bool;
rule {|$result_combine|} $b1 {|@result.null|} ↪ $b1
with {|$result_combine|} $b1 $b1 ↪ $b1
with {|$result_combine|} $b1 $b2 ↪ {|@result.invalid|};
sequential symbol {|$is_pairwise|} [T : Set] [U : Set] : (El T → El T → El U) → (El U → El U → El U) → El T → El {|@List|} → El U → El {|@List|} → El Bool;
rule {|$is_pairwise|} $f $op $a ({|@list|} $b $bs) ($op ▫ ($f ▫ $a ▫ $b) ▫ $B) $rem ↪ {|$is_pairwise|} $f $op $a $bs $B $rem
with {|$is_pairwise|} $f $op $a {|@list.nil|} $B ({|@list|} $b $rem) ↪ {|$is_pairwise|} $f $op $b $rem $B $rem
with {|$is_pairwise|} $f $op $a {|@list.nil|} $nil {|@list.nil|} ↪ {|eo::requires|} $nil ({|eo::nil|} $op ({|eo::typeof|} $a)) true;
sequential symbol {|$extract_pairwise_args_rec|} [T : Set] [U : Set] : (El T → El T → El U) → (El U → El U → El U) → El T → El U → El {|@List|};
rule {|$extract_pairwise_args_rec|} $f $op $a ($op ▫ ($f ▫ $a ▫ $c) ▫ $B) ↪ {|eo::cons|} {|@list|} $c ({|$extract_pairwise_args_rec|} $f $op $a $B)
with {|$extract_pairwise_args_rec|} $f $op $a $B ↪ {|@list.nil|};
sequential symbol {|$extract_pairwise_args|} [T : Set] [U : Set] : (El T → El T → El U) → (El U → El U → El U) → El U → El {|@List|};
rule {|$extract_pairwise_args|} $f $op ($op ▫ ($f ▫ $a ▫ $b) ▫ $B) ↪ let D ≔ $op ▫ ($f ▫ $a ▫ $b) ▫ $B in let elems ≔ {|$extract_pairwise_args_rec|} $f $op $a D in {|eo::requires|} ({|$is_pairwise|} $f $op $a elems D elems) true ({|eo::cons|} {|@list|} $a elems)
with {|$extract_pairwise_args|} $f $op ($f ▫ $a ▫ $b) ↪ {|@list|} $a $b;
constant symbol ite [A : Set] : El Bool → El A → El A → El A;
constant symbol not : El Bool → El Bool;
constant symbol or : El Bool → El Bool → El Bool;
constant symbol and : El Bool → El Bool → El Bool;
constant symbol => : El Bool → El Bool → El Bool;
constant symbol xor : El Bool → El Bool → El Bool;
constant symbol = [A : Set] : El A → El A → El Bool;
sequential symbol {|$get_lambda_type|} : El {|@List|} → Set → Set;
rule {|$get_lambda_type|} ({|@list|} $x $xs) $B ↪ {|eo::typeof|} $x ⤳ ({|$get_lambda_type|} $xs $B)
with {|$get_lambda_type|} {|@list.nil|} $B ↪ $B;
constant symbol lambda [B : Set] (L : El {|@List|}) : El B → El ({|$get_lambda_type|} L B);
constant symbol distinct [A : Set] : El A → El A → El Bool;
constant symbol {|@purify|} [A : Set] (t : El A) : El A;
