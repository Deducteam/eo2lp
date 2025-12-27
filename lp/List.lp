require open Logic.U.Arrow;
require open eo2lp.Core;

injective symbol List : Set → TYPE;

injective symbol ⨾ [a : Set] : El a → List a → List a;
notation ⨾ infix right 5;

symbol ∎ [a : Set] : List a;

symbol nil [a b] :
  El (a ⤳ b ⤳ b) → El b;

symbol cons [a b]
  : El (a ⤳ b ⤳ b) → El a → El b → El b
  ≔ λ f x xs, f ▫ x ▫ xs;

symbol fold [a b] :
  El (a ⤳ b ⤳ b) → List a → El b;

rule fold $f ∎          ↪ nil $f
with fold $f ($x ⨾ $xs) ↪ $f $x (fold $f $xs);


symbol ++ [a] : List a → List a → List a;
notation ++ infix right 5;

rule ∎ ++ $ys ↪ $ys
with $xs ++ ∎ ↪ $xs
with ($x ⨾ $xs) ++ $ys ↪ $x ⨾ ($xs ++ $ys);

sequential symbol
  ite [T : Set] : El Bool → El T → El T → El T;
rule ite true $t1 _ ↪ $t1
with ite false _ $t2 ↪ $t2;

sequential symbol
  eq [T : Set]
  : El T → El T → El Bool;
rule eq $t $t ↪ true
with eq _ _ ↪ false;



symbol halt [a] : El a;

sequential symbol
  list_concat [a b] (f : El (a ⤳ b ⤳ b))
  : El b → El b → El b;
rule
    list_concat $f ($f ▫ $x ▫ $xs) $ys
  ↪
    $f ▫ $x ▫ (list_concat $f $xs $ys)
with
    list_concat $f $xs $ys
  ↪
    ite (eq $xs (nil $f)) $ys
    (ite (eq $ys (nil $f)) $xs halt);

// disjunction. :right-assoc-nil.
constant symbol or
  : El (Bool ⤳ Bool ⤳ Bool);
rule nil or ↪ true;

symbol c1 ≔ (cons or true (cons or true (nil or)));
symbol c2 ≔ (cons or false (cons or false (nil or)));

compute list_concat or c1 c2;
// builtin list type.
constant symbol {|eo::List|}
  : Set;
constant symbol {|eo::List::nil|}
  : El {|eo::List|};
constant symbol {|eo::List::cons|} [a : Set]
  : El (a ⤳ {|eo::List|} ⤳ {|eo::List|});

rule nil {|eo::List::cons|} ↪ {|eo::List::nil|};

//  {|eo::list_concat|} $f
//    ($f ▫ $x ▫ $xs) (f ▫ $y ▫ $ys)
//  ↪
//    ($f ▫ $x ▫ ({|eo::list_concat|} $xs $ys));
symbol {|@List|} ≔ {|eo::List|};
symbol {|@list|} [a : Set]
  : El (a ⤳ {|eo::List|} ⤳ {|eo::List|})
  ≔ λ x xs, {|eo::List::cons|} ▫ x ▫ xs;

symbol {|@list.nil|} ≔ {|eo::List::nil|};

sequential symbol foo : El ({|@List|} ⤳ Bool);
rule foo
  ({|eo::List::cons|} ▫ $x ▫ $xs) ↪ false
with foo ({|eo::List::nil|}) ↪ true;

symbol xs : El {|@List|};
compute
  {|eo::List::cons|} ▫ true ▫
  (list_concat {|eo::List::cons|} xs {|eo::List::nil|});

compute foo ({|eo::List::cons|} ▫ true ▫
  (list_concat {|eo::List::cons|} {|eo::List::nil|} {|eo::List::nil|}));
