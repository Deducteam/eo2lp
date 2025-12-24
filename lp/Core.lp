require open Logic.U.Set Logic.U.Arrow;

symbol Bool : Set;
symbol true : El Bool;
symbol false : El Bool;

symbol List : Set → TYPE;

symbol {|eo::List|} : Set;
symbol {|eo::List::nil|} : El {|eo::List|};
symbol {|eo::List::cons|} [a : Set]
  : El (a ⤳ {|eo::List|} ⤳ {|eo::List|});

sequential symbol {|eo::list_concat|} [a b : Set] :
  El (a ⤳ b ⤳ b) → El b → El b → El b;
rule {|eo::list_concat|} $f
    ($f ▫ $x ▫ $xs) (f ▫ $y ▫ $ys)
  ↪
    ($f ▫ $x ▫ ({|eo::list_concat|} $xs $ys))
with
  ;

symbol {|@List|} ≔ {|eo::List|};
symbol {|@list|} [a] ≔ {|eo::List::cons|} [a];
symbol {|@list.nil|} ≔ {|eo::List::nil|};

sequential symbol foobar : El ({|@List|} ⤳ Bool);
rule (foobar ({|@list|} $x $xs)) ↪ false
with (foobar {|@list.nil|}) ↪ true;

rule (foobar ({|@list|} $x ())) ↪ false
with (foobar {|@list.nil|}) ↪ true;


constant symbol ▫ [α : Set] [β : Set]
  : El (α ⤳ β) → El α → El β;
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


sequential symbol
 {|eo::add|} [T : Set] [S : Set] : El T → El T → El S;
