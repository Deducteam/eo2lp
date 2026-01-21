# eo2lp: Project History and Recent Advancements

## Overview

**eo2lp** is an OCaml tool that translates signatures and proof scripts from **Eunoia** (a proof language for SMT solvers like cvc5) to **LambdaPi** (a logical framework for proof formalization based on the λΠ-calculus modulo rewriting).

The project bridges two worlds: the SMT solving community's need for certified proofs, and the proof assistant interoperability ecosystem centered around LambdaPi.

## Project Timeline

### Phase 1: Initial Development (March 2025)

The project began in early March 2025 with the goal of translating cvc5's proof output to LambdaPi.

**Key milestones:**
- **March 3**: Initial commit with basic infrastructure
- **March 5-6**: First successful proof checking in LambdaPi
- **March 7**: Dependency handling between modules
- **March 12**: Program-schema mechanism for handling Eunoia programs
- **March 18-21**: Support for congruence rules (`cong`, `nary_cong`)
- **March 26**: **All 30 Rodin benchmark proofs successfully checked**

This phase established that the translation approach was viable, successfully checking QF-UF (quantifier-free uninterpreted functions) proofs from the Rodin SMT-LIB benchmark.

### Phase 2: Formalization and Paper Writing (August-October 2025)

After a hiatus, work resumed in August 2025 with a focus on formalizing the translation and preparing a paper.

**Key activities:**
- **August 4-12**: Paper writing began; formal grammar for Eunoia specified
- **October 7-17**: LambdaPi specification completed; collaboration with Guillaume Burel
- **October 15-17**: Paper finalized for initial submission

This phase produced a formal specification of both the source (Eunoia) and target (LambdaPi) languages, along with the translation semantics.

### Phase 3: Major Refactoring (November-December 2025)

Starting in November 2025 (during a visit to Brazil), the codebase underwent significant refactoring to support more of CPC and improve the architecture.

**November 2025:**
- **Nov 10**: Begin major refactoring effort
- **Nov 11-12**: Complete parser rewrite using modern Menhir patterns
- **Nov 17-18**: New signature processing pipeline
- **Nov 20-24**: New elaboration system with support for `:binder` attributes
- **Nov 22-26**: LambdaPi syntax AST and pretty-printing
- **Nov 27**: Type constructor applications (`TyApp`) distinguished from term applications

**December 2025:**
- **Dec 2-5**: Type inference algorithm development (meetings with Guillaume)
- **Dec 19-27**: Schematic variable binding; handling of implicit parameters in rewrite rules

Key insight from this phase: Implicit parameter insertion on the RHS of rewrite rules causes unification failures with pattern variables. The solution is to only insert explicits on the LHS.

### Phase 4: Overloading and LambdaPi Integration (January 2026)

The current phase addresses one of the hardest problems: symbol overloading.

**The Overloading Problem:**
Eunoia allows symbol overloading (e.g., `-` is both binary subtraction and unary negation). Resolution requires type information that may only be available after rewriting.

**Solution:** Use LambdaPi as an external typechecker during translation. When encountering overloaded symbols, query LambdaPi to determine which variant produces a well-typed term.

**Recent advancements (January 2026):**
- **Jan 6**: Design of LambdaPi-as-typechecker approach for overloading
- **Jan 11-19**: Implementation of new tree-based UI for debugging output
- **Jan 19**: Checkpoint with working tree UI and improved translation

## Architecture Evolution

### Original Architecture (March 2025)
```
.eo files → Parser → Simple AST → Direct Translation → .lp files
```

### Current Architecture (January 2026)
```
.eo files → Lexer/Parser → Eunoia AST
                              ↓
                    Signature Graph (dependency analysis)
                              ↓
                    Elaboration (type inference, overload resolution)
                              ↓
                    Encoding (to LambdaPi AST)
                              ↓
                    Output (.lp files with proper imports)
```

**Key components:**
- `syntax_eo.ml` - Eunoia AST, signature graphs, symbol tables
- `elaborate.ml` - Term elaboration with metavariable handling
- `encode.ml` - Translation to LambdaPi
- `syntax_lp.ml` - LambdaPi AST
- `Prelude.lp` - Core Eunoia builtin symbols

## Technical Challenges and Solutions

### 1. N-ary Operators
Eunoia supports n-ary operators with various associativity attributes (`:right-assoc-nil`, `:left-assoc-nil`, `:chainable`, `:pairwise`).

**Solution:** Elaborate n-ary applications to binary form during the elaboration phase, respecting the declared associativity and nil terminators.

### 2. Dependent Types
Eunoia types can depend on terms (e.g., `BitVec n` where `n` is an integer).

**Solution:** Use LambdaPi's dependent type system directly. Types are translated to terms in the `Set` universe, with `El` (elements) and `τ` for type coercion.

### 3. Programs as Rewrite Rules
Eunoia programs define computation via pattern matching, which maps naturally to LambdaPi's rewrite rules.

**Challenge:** Eunoia programs have typed pattern variables in their context, but LambdaPi infers types from patterns.

**Solution:** Insert explicit type annotations on the LHS of rewrite rules to help LambdaPi infer pattern variable types. Avoid RHS insertions as they cause unification failures.

### 4. Proof Script Translation
Eunoia proof scripts use `assume` and `step` commands to build derivations.

**Solution:** Translate to LambdaPi symbol declarations where proofs are terms inhabiting proposition types (proofs-as-programs via Curry-Howard).

## Current Status (January 2026)

**Working:**
- Full parsing of Eunoia files
- Signature graph construction with cycle detection
- Elaboration with type inference
- Translation of declarations, definitions, programs, and rules
- Tree-based debugging UI
- Successful translation of `programs/Utils`, `programs/Nary`, `programs/Arith`

**In Progress:**
- Overload resolution via LambdaPi queries
- Support for full CPC (arithmetic, strings, bit-vectors)
- Scaling to larger proofs

**Test Results (cpc-mini):**
- 3 modules passing full type-checking
- Several modules with minor type preservation issues being addressed

## Future Directions

1. **Complete CPC Support:** Extend to arithmetic, strings, bit-vectors, arrays, datatypes
2. **Proof Scaling:** Handle industrial-scale proofs from cvc5
3. **Elaboration in LambdaPi:** Potentially move more elaboration logic to LambdaPi itself
4. **SMT-LIB 3 Integration:** As Eunoia evolves with SMT-LIB 3 proposals

## References

- **Eunoia**: https://github.com/cvc5/ethos
- **LambdaPi**: https://github.com/Deducteam/lambdapi
- **cvc5**: https://cvc5.github.io/
- **CPC (Co-operating Proof Calculus)**: cvc5's proof system formalized in Eunoia

## Contributors

- Ciarán Dunne (ENS Paris-Saclay)
- Guillaume Burel (INRIA)
