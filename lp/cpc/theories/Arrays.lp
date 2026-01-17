require open cpc.Core Stdlib.Set cpc.theories.Builtin;
constant symbol Array : τ (eo⋅⋅Type ⤳ eo⋅⋅Type ⤳ eo⋅⋅Type);
constant symbol select [U : Set] [T : Set]: τ ((Array U T) ⤳ U ⤳ T);
constant symbol store [U : Set] [T : Set]: τ ((Array U T) ⤳ U ⤳ T ⤳ Array U T);
constant symbol {|@array_deq_diff|} [T : Set] [U : Set] (a : τ (Array T U)) (b : τ (Array T U)): τ T;
