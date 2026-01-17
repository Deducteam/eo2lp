require open cpc.Core Stdlib.Set cpc.theories.ArithBvConv cpc.programs.Arith cpc.programs.Utils;
sequential symbol !abconv_ubv_to_int_elim [n : τ Int]: τ ((BitVec n) ⤳ Int ⤳ Int ⤳ Int ⤳ Int);
rule !abconv_ubv_to_int_elim ($b) ($w) ($w) ($p) ↪ 0
with !abconv_ubv_to_int_elim ($b) ($i) ($w) ($p) ↪ eo⋅⋅cons + (ite (and (= (extract ($i) ($i) ($b)) ())) ($p) (0)) (!abconv_ubv_to_int_elim ($b) (eo⋅⋅add ($i) (1)) ($w) (eo⋅⋅mul ($p) (2)));
sequential symbol !abconv_int_to_bv_elim [w : τ Int]: τ (Int ⤳ (eo⋅⋅quote w) ⤳ Int ⤳ BitVec w);
rule !abconv_int_to_bv_elim ($n) (0) ($p) ↪ {|@bv_empty|}
with !abconv_int_to_bv_elim ($n) ($w) ($p) ↪ (let wm1 ≔ eo⋅⋅add ($w) (-1) in (let pd2 ≔ eo⋅⋅zdiv ($p) (2) in eo⋅⋅cons concat (ite (and (>= (mod_total ($n) ($p)) pd2)) () ()) (!abconv_int_to_bv_elim ($n) wm1 pd2)));
