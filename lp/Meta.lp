//require open eo2lp.Core;
require open
  Stdlib.HOL
  Stdlib.List
  Stdlib.String
  Stdlib.Z
  Stdlib.Bool;

// set of all `eo` terms.
symbol eo : Set;
//sequential symbol ty : τ eo → TYPE;


// if we have `meta`, we can do typechecking here?
// once a term is typechecked and elaborated,
// we inject into the 'real' translated file?
symbol ITE : 𝔹 → Set → Set → Set;

symbol ctyp : String → τ eo → 𝔹;
//symbol catt : String → τ;
symbol typeof : τ (eo ⤳ eo);

//symbol tm (t : τ eo) : ITE (ctyp ) ty (typeof t);

symbol 𝒦 : τ eo;
symbol const : String → τ eo → τ eo;

symbol ty ≔ const "Type" 𝒦;
symbol b  ≔ const "Bool" (const "Type" 𝒦);

symbol var : String → τ eo → τ eo;
symbol app : String → τ (list eo) → τ eo;

symbol __ : τ eo → τ eo → τ eo;
compute app "-" (var "x" b ⸬ var "y" b ⸬ □);



// align Eunoia `Type` with `Set`.
symbol EO_TYPE ≔ const "Type" EO_KIND;
rule ty (const "Type" EO_KIND) ↪ Set;

rule ty (app "->" ($t ⸬ □))   ↪ ty $t
with ty (app "->" ($t ⸬ $ts)) ↪ ty $t → ty (app "->" $ts);

// align Eunoia `Bool` constant with `𝔹`.
symbol EO_BOOL ≔ const "Bool" EO_TYPE;
rule ty (const "Bool" (const "Type" EO_KIND)) ↪ 𝔹;

symbol EO_INT ≔ const "Int" EO_TYPE;
rule ty (const "Int" EO_TYPE) ↪ ℤ;

compute ty
    (app "->" (EO_BOOL ⨾ EO_BOOL ⨾ ∎));

type const "@@Pair" (app "->" (EO_TYPE ⨾ EO_TYPE ⨾ EO_TYPE ⨾ ∎));

type const "-" (app "->" (EO_INT ⨾ EO_INT ⨾ ∎));
type const "-" (app "->" (EO_INT ⨾ EO_INT ⨾ EO_INT ⨾ ∎));


symbol _Z : ℤ → τ eo;

compute
  app "-" (_Z 1 ⨾ ∎);
compute
  app "-" (_Z 2 ⨾ _Z 2 ⨾ ∎);


// in this setup, is there any way to ask
// 'is t well typed?'

symbol ite : τ eo → τ eo → τ eo → τ eo;
rule ite (const "true" bool) $x $y ↪ $x;






symbol eo∷List ≔ const "eo::List" Type;
symbol eo∷List∷nil ≔ const "eo::List::nil" Type;
symbol eo∷List∷cons ≔ const "eo::List::cons" Type;

symbol !!Pair ≔ const "@@Pair" (arrow (Type ⨾ Type ⨾ ∎));
symbol !Pair ≔ !!Pair;



symbol !List ≔ eo∷List;
symbol !List_nil  ≔ eo∷List∷nil;
symbol !List_cons ≔ eo∷List∷cons;
