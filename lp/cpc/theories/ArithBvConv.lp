require open cpc.Core Stdlib.Set cpc.theories.BitVectors cpc.theories.Ints;
constant symbol int_to_bv (w : τ Int): τ (Int ⤳ BitVec w);
constant symbol ubv_to_int [m : τ Int]: τ ((BitVec m) ⤳ Int);
constant symbol sbv_to_int [m : τ Int]: τ ((BitVec m) ⤳ Int);
symbol int2bv ≔ int_to_bv;
symbol bv2nat ≔ ubv_to_int;
