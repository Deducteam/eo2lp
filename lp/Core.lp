require open Logic.U.Set Logic.U.Arrow;

symbol Bool : Set;
symbol true : El Bool;
symbol false : El Bool;

constant symbol ▫ [α : Set] [β : Set] : El (α ⤳ β) → El α → El β;
notation ▫ infix left 5;

constant symbol ⊙ : (Set → Set) → Set → Set;

sequential symbol
  {|eo::ite|} [T : Set] : El Bool → El T → El T → El T;
rule {|eo::ite|} true  $t1 $t2 ↪ $t1
with {|eo::ite|} false $t1 $t2 ↪ $t2;

sequential symbol
  {|eo::eq|} [T : Set] : El T → El T → El Bool;
rule {|eo::eq|} $t $t ↪ true
with {|eo::eq|} _   _ ↪ false;

sequential symbol
  {|eo::gt|} [T : Set] : El T → El T → El Bool;




symbol {|eo::numeral|} : Set;
symbol {|eo::rational|} : Set;
//symbol NONE : Set;

// declare-consts <numeral> Int
//symbol magic [a : Set] : El (NONE ⤳ a);
//coerce_rule coerce (El NONE) (El $a) $x ↪ magic $x;
symbol Int : Set;
symbol z : El Int;

sequential symbol
 {|eo::add|} [T : Set] [S : Set] : El T → El T → El S;

rule {|eo::add|} [Int] [Int] z z ↪ z;

type {|eo::add|} ({|eo::add|} true true) z;

assert ⊢ () : El Bool;
