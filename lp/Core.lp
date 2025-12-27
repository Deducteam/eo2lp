require open Logic.U.Set Logic.U.Arrow;

// object-level application.
constant symbol ▫ [a b]
  : El (a ⤳ b) → El a → El b;
notation ▫ infix left 5;
