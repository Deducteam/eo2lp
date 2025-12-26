require open Logic.U.Set Logic.U.Arrow;

symbol Bool : Set;
symbol true : El Bool;
symbol false : El Bool;

// object-level application.
constant symbol ▫ [a b]
  : El (a ⤳ b) → El a → El b;
notation ▫ infix left 5;

sequential symbol
  ite [T : Set] : El Bool → El T → El T → El T;
rule ite true $t1 _ ↪ $t1
with ite false _ $t2 ↪ $t2;

sequential symbol
  eq [T : Set]
  : El T → El T → El Bool;
rule eq $t $t ↪ true
with eq _ _ ↪ false;

symbol nil [a b] :
  El (a ⤳ b ⤳ b) → El b;

symbol cons [a b]
  : El (a ⤳ b ⤳ b) → El a → El b → El b
  ≔ λ f x xs, f ▫ x ▫ xs;

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
// (or x y z)
// --> (or [x;y;z])
//
// (or x xs)
// --> (or (x ; ∎) ++ or xs ++ or (y ; ∎))

// this would be nice, but this means f-lists
// wont match on programs that use the ordinary
// application structure.

// the patterns of programs need to be in 'normal form'.
// fortunately (@list x xs) elaborates to
//    (eo::List::cons x
//      (eo::list_concat eo::List::cons xs eo::List::nil)
//    )
// which elaborates to
//    (eo::List::cons x xs)
// so we can 'hard-wire' this during desugaring.


constant symbol ⊙ : (Set → Set) → Set → Set;


symbol Proof : El Bool → TYPE;
symbol rps : El (Bool ⤳ Bool ⤳ Bool);
symbol ps [F] (C : El Bool) : Proof (F) → Proof (rps F C);

sequential symbol
  {|eo::gt|} [T : Set] : El T → El T → El Bool;


symbol {|eo::numeral|} : Set;
symbol {|eo::rational|} : Set;


sequential symbol
 {|eo::add|} [T : Set] [S : Set] : El T → El T → El S;
