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
