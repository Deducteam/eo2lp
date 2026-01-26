require cpc.Prelude as eo;
require open cpc.theories.Builtin cpc.theories.Reals cpc.theories.Ints;

sequential symbol {|$greatest_int_lt|} [R : Set] : τ (R ⤳ {|eo::Int|});
rule @{|$greatest_int_lt|} ($R) ($c) ↪ let ci ≔ @{|eo::to_z|} _ $c in @{|eo::ite|} _ _ (@{|eo::eq|} _ _ (@{|eo::to_q|} _ $c) (@{|eo::to_q|} _ ci)) (@{|eo::add|} _ _ -1 ci) ci;
sequential symbol {|$least_int_gt|} [R : Set] : τ (R ⤳ Int);
rule @{|$least_int_gt|} ($R) ($c) ↪ @{|eo::add|} {|eo::Int|} {|eo::Int|} 1 (@{|eo::to_z|} $R $c);
