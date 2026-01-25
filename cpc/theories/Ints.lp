require cpc.Prelude as eo;
require open cpc.theories.Arith;

constant symbol div : τ ({|eo::Int|} ⤳ ({|eo::Int|} ⤳ {|eo::Int|}));
constant symbol mod : τ ({|eo::Int|} ⤳ ({|eo::Int|} ⤳ {|eo::Int|}));
constant symbol divisible : τ ({|eo::Int|} ⤳ ({|eo::Int|} ⤳ Bool));
constant symbol {|int.pow2|} : τ ({|eo::Int|} ⤳ {|eo::Int|});
constant symbol {|int.log2|} : τ ({|eo::Int|} ⤳ {|eo::Int|});
constant symbol {|int.ispow2|} : τ ({|eo::Int|} ⤳ Bool);
constant symbol div_total : τ ({|eo::Int|} ⤳ ({|eo::Int|} ⤳ {|eo::Int|}));
constant symbol mod_total : τ ({|eo::Int|} ⤳ ({|eo::Int|} ⤳ {|eo::Int|}));
constant symbol {|@int_div_by_zero|} : τ ({|eo::Int|} ⤳ {|eo::Int|});
constant symbol {|@mod_by_zero|} : τ ({|eo::Int|} ⤳ {|eo::Int|});
