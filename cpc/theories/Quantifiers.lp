require cpc.Prelude as eo;
require open cpc.programs.Utils cpc.programs.Nary cpc.theories.Arith;

constant symbol forall : τ ({|eo::List|} ⤳ (Bool ⤳ Bool));
constant symbol exists : τ ({|eo::List|} ⤳ (Bool ⤳ Bool));
sequential symbol {|$get_var_list|} : τ (Bool ⤳ {|eo::List|});
constant symbol {|@quantifiers_skolemize|} : Π v280: (τ Bool → τ {|eo::Int|} → Set), Π v281: (τ Bool → τ {|eo::Int|} → Set), Π v282: (τ Bool → τ {|eo::Int|} → Set), Π F: τ Bool, Π i: τ {|eo::Int|}, τ (@APP {|eo::Int|} {|eo::Type|} (@APP {|eo::List|} ({|eo::Int|} ⤳ {|eo::Type|}) (@APP ({|eo::Type|} ⤳d (λ T: Set, T ⤳ ({|eo::List|} ⤳ {|eo::List|}))) ({|eo::List|} ⤳ ({|eo::Int|} ⤳ {|eo::Type|})) (@{|$assoc_nil_nth_type|} v282 v281 v280 {|eo::List|}) @{|eo::List::cons|}) (@APP Bool {|eo::List|} {|$get_var_list|} F)) i);
