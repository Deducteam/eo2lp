# eo2lp

Translates [Eunoia](https://github.com/cvc5/ethos/blob/main/user_manual.md) proof signatures and scripts to [LambdaPi](https://github.com/Deducteam/lambdapi), enabling verification of [cvc5](https://cvc5.github.io/) SMT solver proofs in the [Dedukti](https://deducteam.github.io/) ecosystem.

Currently handles CPC-MINI, a 22-module subset of cvc5's Cooperating Proof Calculus. All generated LambdaPi files pass type checking with subject reduction. On a benchmark of 1,036 proofs across 14 SMT-LIB fragments, 97% pass LambdaPi verification.

## Building

Requires OCaml, Dune, and LambdaPi (as an opam library).

```bash
dune build
dune test
```

## Usage

```bash
# Translate CPC-MINI signature (cpc/ → _build/cpc/)
dune exec eo2lp

# Translate and verify proofs
dune exec eo2lp -- --proofs proofs/QF_UF --check --timeout 5

# Custom input/output, verbose
dune exec eo2lp -- -d <input_dir> -o <output_dir> -v info
```

Generated `.lp` files can be checked independently:

```bash
cd _build/cpc && lambdapi check Cpc.lp
```

Run `dune exec eo2lp -- --help` for the full list of options.

## Translation pipeline

```
.eo files → [Parse] → Eunoia AST → [Elaborate] → [Encode] → .lp files
```

1. **Parsing** (`lexer.mll`, `parser.mly`): produces an Eunoia AST. Module dependencies are resolved from `include` directives, and modules are topologically sorted.

2. **Elaboration** (`elaborate.ml`): rewrites EO terms into a normalized form — resolves overloads, expands n-ary operators to binary, handles binders and argument lists, expands defines. No LP-specific logic.

3. **Encoding** (`encode.ml`): translates elaborated EO terms to LambdaPi `Core.Term` values. Eunoia types are lifted via `tau : Set → TYPE`. Implicit arguments are filled by LambdaPi's type inference (`resolve.ml`). Core builtins are defined in `Prelude.lp`.

## Scripts

```bash
./scripts/bench.sh proofs --results results.csv --timeout 5   # parallel benchmark
./scripts/gen-results-table.sh results.csv > tex/results-table.tex
./scripts/gen-proofs.sh                                        # generate proofs from SMT-LIB
./scripts/diff-cpc.sh                                         # compare cpc/ with upstream cvc5
```

## License

This project is under development.
