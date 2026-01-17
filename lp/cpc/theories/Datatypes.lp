require open cpc.Core Stdlib.Set cpc.programs.Nary;
constant symbol is [C : Set] [D : Set]: τ (C ⤳ D ⤳ Bool);
constant symbol update [D : Set] [T : Set] [S : Set]: τ (S ⤳ D ⤳ T ⤳ D);
constant symbol UnitTuple : Set;
constant symbol Tuple : τ (eo⋅⋅Type ⤳ eo⋅⋅Type ⤳ eo⋅⋅Type);
constant symbol tuple⋅unit : τ UnitTuple;
constant symbol tuple [T : Set] [U : Set]: τ (T ⤳ U ⤳ eo⋅⋅cons Tuple T U);
constant symbol tuple⋅select [T : Set] (i : τ Int): τ (T ⤳ eo⋅⋅list_nth Tuple T i);
constant symbol tuple⋅update [T : Set] [U : Set] (i : τ Int): τ (T ⤳ U ⤳ eo⋅⋅requires U (eo⋅⋅list_nth Tuple T i) T);
