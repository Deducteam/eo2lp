require cpc.Prelude as eo;
require open cpc.theories.Builtin;

sequential symbol {|$extract_antec_rec|} : τ (Bool ⤳ (Bool ⤳ Bool));
sequential symbol {|$extract_antec|} : τ (Bool ⤳ (Bool ⤳ Bool));
sequential symbol {|$run_process_scope|} : τ (Bool ⤳ (Bool ⤳ Bool));
