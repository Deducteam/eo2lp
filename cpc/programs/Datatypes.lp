require cpc.Prelude as eo;
require open cpc.theories.Datatypes;

sequential symbol {|$dt_get_constructors|} : Π U: Set, τ (U ⤳ {|eo::List|});
sequential symbol {|$tuple_get_selectors_rec|} : τ ({|eo::Type|} ⤳ ({|eo::Int|} ⤳ {|eo::List|}));
sequential symbol {|$dt_get_selectors|} : Π T: Set, τ ({|eo::Type|} ⤳ (T ⤳ {|eo::List|}));
sequential symbol {|$dt_get_selectors_of_app|} : Π T: Set, τ ({|eo::Type|} ⤳ (T ⤳ {|eo::List|}));
symbol {|$dt_is_cons|} [T : Set] (t : τ T) ≔ @{|eo::ite|} Bool Bool (@{|eo::is_eq|} T ({|eo::Type|} ⤳d (λ T: Set, {|eo::Type|} ⤳d (λ U: Set, T ⤳ (U ⤳ @{|eo::cons|} {|eo::Type|} {|eo::Type|} Tuple T U)))) t @tuple) true (@{|eo::is_ok|} {|eo::List|} (@{|eo::dt_selectors|} T t));
sequential symbol {|$dt_arg_list|} : Π T: Set, τ (T ⤳ {|eo::List|});
sequential symbol {|$dt_eq_cons|} : Π T: Set, Π V: Set, τ (T ⤳ (V ⤳ Bool));
sequential symbol {|$tuple_nth|} : Π T: Set, Π n: τ {|eo::Int|}, τ (T ⤳ (@{|eo::quote|} {|eo::Type|} n ⤳ @{|eo::list_nth|} {|eo::Type|} {|eo::Type|} Tuple T n));
