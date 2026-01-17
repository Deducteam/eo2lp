require open cpc.Core Stdlib.Set cpc.theories.Builtin;
constant symbol Int : Set;
constant symbol Real : Set;
sequential symbol !arith_typeunion : τ (eo⋅⋅Type ⤳ eo⋅⋅Type ⤳ eo⋅⋅Type);
rule !arith_typeunion Int Int ↪ Int
with !arith_typeunion Real Real ↪ Real
with !arith_typeunion Real Int ↪ Real
with !arith_typeunion Int Real ↪ Real;
sequential symbol !is_arith_type : τ (eo⋅⋅Type ⤳ Bool);
rule !is_arith_type Int ↪ true
with !is_arith_type Real ↪ true;
constant symbol + [T : Set] [U : Set]: τ (T ⤳ U ⤳ !arith_typeunion T U);
constant symbol * [T : Set] [U : Set]: τ (T ⤳ U ⤳ !arith_typeunion T U);
constant symbol < [T : Set] [U : Set]: τ (T ⤳ U ⤳ eo⋅⋅requires (!is_arith_type T) true (eo⋅⋅requires (!is_arith_type U) true Bool));
constant symbol <= [T : Set] [U : Set]: τ (T ⤳ U ⤳ eo⋅⋅requires (!is_arith_type T) true (eo⋅⋅requires (!is_arith_type U) true Bool));
constant symbol > [T : Set] [U : Set]: τ (T ⤳ U ⤳ eo⋅⋅requires (!is_arith_type T) true (eo⋅⋅requires (!is_arith_type U) true Bool));
constant symbol >= [T : Set] [U : Set]: τ (T ⤳ U ⤳ eo⋅⋅requires (!is_arith_type T) true (eo⋅⋅requires (!is_arith_type U) true Bool));
constant symbol to_real [T : Set]: τ (T ⤳ eo⋅⋅requires (!is_arith_type T) true Real);
constant symbol to_int [T : Set]: τ (T ⤳ eo⋅⋅requires (!is_arith_type T) true Int);
constant symbol is_int [T : Set]: τ (T ⤳ eo⋅⋅requires (!is_arith_type T) true Bool);
constant symbol abs [T : Set]: τ (T ⤳ eo⋅⋅requires (!is_arith_type T) true T);
constant symbol - [T : Set]: τ (T ⤳ eo⋅⋅requires (!is_arith_type T) true T);
