require open Logic.U.Set Logic.U.Arrow;

// object-level application.
constant symbol ▫ [a b]
  : El (a ⤳ b) → El a → El b;
notation ▫ infix left 5;

constant symbol {|eo::requires_type_in|}
  [U : Set] : Set → Set → El U → El U;

constant symbol {|eo::requires_type_out|}
  [U : Set] : El U → El U → Set → Set;
