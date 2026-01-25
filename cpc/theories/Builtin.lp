require cpc.Prelude as eo;
require open cpc.programs.Utils;

constant symbol ite : Π A: Set, τ (Bool ⤳ (A ⤳ (A ⤳ A)));
constant symbol not : τ (Bool ⤳ Bool);
constant symbol or : τ (Bool ⤳ (Bool ⤳ Bool));
constant symbol and : τ (Bool ⤳ (Bool ⤳ Bool));
constant symbol => : τ (Bool ⤳ (Bool ⤳ Bool));
constant symbol xor : τ (Bool ⤳ (Bool ⤳ Bool));
constant symbol = : Π A: Set, τ (A ⤳ (A ⤳ Bool));
sequential symbol {|$get_lambda_type|} : τ ({|eo::List|} ⤳ ({|eo::Type|} ⤳ {|eo::Type|}));
constant symbol lambda : Π B: Set, Π L: τ {|@List|}, τ (B ⤳ @APP {|eo::Type|} {|eo::Type|} (@APP {|@List|} ({|eo::Type|} ⤳ {|eo::Type|}) {|$get_lambda_type|} L) B);
constant symbol {|@purify|} : Π A: Set, τ A → τ A;
