require open cpc.Core Stdlib.Set cpc.programs.Utils;
constant symbol ite [A : Set]: τ (Bool ⤳ A ⤳ A ⤳ A);
constant symbol not : τ (Bool ⤳ Bool);
constant symbol or : τ (Bool ⤳ Bool ⤳ Bool);
constant symbol and : τ (Bool ⤳ Bool ⤳ Bool);
constant symbol => : τ (Bool ⤳ Bool ⤳ Bool);
constant symbol xor : τ (Bool ⤳ Bool ⤳ Bool);
constant symbol = [A : Set]: τ (A ⤳ A ⤳ Bool);
sequential symbol !get_lambda_type : τ ({|@List|} ⤳ eo⋅⋅Type ⤳ eo⋅⋅Type);
rule !get_lambda_type ({|@list|} ($x) ($xs)) ($B) ↪ (eo⋅⋅typeof ($x)) ⤳ !get_lambda_type ($xs) ($B)
with !get_lambda_type {|@list.nil|} ($B) ↪ $B;
constant symbol lambda [B : Set] (L : τ {|@List|}): τ (B ⤳ !get_lambda_type L B);
constant symbol distinct (xs : τ {|@List|}): τ (eo⋅⋅requires (!assoc_nil_same_type {|@list|} xs) true Bool);
constant symbol {|@purify|} [A : Set] (t : τ A): τ A;
