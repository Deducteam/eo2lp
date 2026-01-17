require open cpc.Core Stdlib.Set cpc.theories.Builtin;
sequential symbol !extract_antec_rec : τ (Bool ⤳ Bool ⤳ Bool);
rule !extract_antec_rec ($C) ($C) ↪ true
with !extract_antec_rec (=> ($F1) ($F2)) ($C) ↪ eo⋅⋅cons and ($F1) (!extract_antec_rec ($F2) ($C));
sequential symbol !extract_antec : τ (Bool ⤳ Bool ⤳ Bool);
rule !extract_antec (=> ($F) ($C)) ($C) ↪ $F
with !extract_antec ($F) ($C) ↪ !extract_antec_rec ($F) ($C);
sequential symbol !run_process_scope : τ (Bool ⤳ Bool ⤳ Bool);
rule !run_process_scope ($F) false ↪ not (!extract_antec ($F) false)
with !run_process_scope ($F) ($C) ↪ => (!extract_antec ($F) ($C)) ($C);
