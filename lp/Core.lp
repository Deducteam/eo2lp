require open Logic.U.Set Logic.U.Arrow;

// object-level application.
constant symbol ▫ [a b]
  : El (a ⤳ b) → El a → El b;
notation ▫ infix left 5;

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
