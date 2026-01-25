require cpc.Prelude as eo;
require open cpc.theories.Builtin;

constant symbol Int : Set;
constant symbol Real : Set;
sequential symbol {|$arith_typeunion|} : τ ({|eo::Type|} ⤳ ({|eo::Type|} ⤳ {|eo::Type|}));
sequential symbol {|$is_arith_type|} : τ ({|eo::Type|} ⤳ Bool);
constant symbol + : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @APP {|eo::Type|} {|eo::Type|} (@APP {|eo::Type|} ({|eo::Type|} ⤳ {|eo::Type|}) {|$arith_typeunion|} T) U));
constant symbol - : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @APP {|eo::Type|} {|eo::Type|} (@APP {|eo::Type|} ({|eo::Type|} ⤳ {|eo::Type|}) {|$arith_typeunion|} T) U));
constant symbol * : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @APP {|eo::Type|} {|eo::Type|} (@APP {|eo::Type|} ({|eo::Type|} ⤳ {|eo::Type|}) {|$arith_typeunion|} T) U));
constant symbol < : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true (@{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} U) true Bool)));
constant symbol <= : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true (@{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} U) true Bool)));
constant symbol > : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true (@{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} U) true Bool)));
constant symbol >= : Π T: Set, Π U: Set, τ (T ⤳ (U ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true (@{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} U) true Bool)));
constant symbol to_real : Π T: Set, τ (T ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true {|eo::Rat|});
constant symbol to_int : Π T: Set, τ (T ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true {|eo::Int|});
constant symbol is_int : Π T: Set, τ (T ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true Bool);
constant symbol abs : Π T: Set, τ (T ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true T);
constant symbol -' : Π T: Set, τ (T ⤳ @{|eo::requires|} Bool Bool {|eo::Type|} (@APP {|eo::Type|} Bool {|$is_arith_type|} T) true T);
