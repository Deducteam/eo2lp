require open Logic.U.Set Logic.U.Arrow;

symbol nat : Set;

symbol zero : El nat;
symbol succ : El (nat ⤳ nat);
symbol one : El nat ≔ succ zero;


builtin "0" ≔ zero;
builtin "1" ≔ one;


builtin "nat_zero" ≔ zero;
builtin "nat_succ" ≔ succ;

type 2;
