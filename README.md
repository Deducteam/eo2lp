# eo2lp

Translate proof signatures and scripts from [Eunoia](https://github.com/cvc5/ethos/blob/main/user_manual.md) (cvc5's proof language) to [LambdaPi](https://github.com/Deducteam/lambdapi).

Translates CPC-MINI (a subset of cvc5's Cooperating Proof Calculus covering theories, inference rules, and side-condition programs) with all generated files passing LambdaPi type checking including subject reduction verification. Also translates cvc5 proof scripts from multiple SMT-LIB fragments.

## Building

Requires OCaml, Dune, and LambdaPi (installed as an opam library).

```bash
dune build
```

## Usage

Translate a directory of Eunoia (`.eo`) files to LambdaPi:

```bash
dune exec eo2lp -- -d <input_dir> -o <output_dir>
```

Options:
- `-d <dir>` -- Input directory containing `.eo` files (default: `./cpc`)
- `-o <dir>` -- Output directory for LambdaPi package (default: `./_build/cpc`)
- `-v <level>` -- Log verbosity: `info`, `warn`, or `error`
- `--proofs <dir>` -- Translate `.eo` proof files from the given directory
- `--check` -- Verify generated `.lp` files with `lambdapi check`
- `--bench` -- Benchmark mode (terse output, one line per proof)
- `--timeout <N>` -- Per-proof timeout in seconds
- `--results <file>` -- Write per-proof results to a CSV file
- `--step` -- Show each proof step's EO and LP as it encodes
- `--expert` -- Include files from `expert/` directory
- `--no-color` -- Disable colored output

### Example

```bash
# Translate CPC-MINI with error-level reporting
dune exec eo2lp -- -d cpc -o _build/cpc -v error

# Translate and verify proofs from a fragment
dune exec eo2lp -- --proofs proofs/QF_UF --check --timeout 5

# Full verbose output
dune exec eo2lp -- -v info
```

This will:
1. Parse all `.eo` files and build a dependency graph
2. Topologically sort modules by their include dependencies
3. Encode each module to LambdaPi, generating `.lp` files
4. Verify each generated file with `lambdapi check`

### Verifying Output

Generated `.lp` files can be independently checked with LambdaPi:

```bash
cd _build/cpc && lambdapi check Cpc.lp
```

## Testing

```bash
dune test
```

The test suite covers parsing, Prelude.lp rewrite rule verification, and signature graph construction.

## How It Works

eo2lp implements a 3-phase translation pipeline:

```
.eo files  -->  [Parse]  -->  Eunoia AST  -->  [Elaborate]  -->  [Encode]  -->  .lp files
```

**Parsing**: A Menhir parser (`parser.mly`) and ocamllex tokenizer (`lexer.mll`) produce an Eunoia AST defined in `syntax_eo.ml`. Module dependencies are resolved from `include` directives, cycles are detected, and modules are topologically sorted.

**Elaboration** (`elaborate.ml`): EO term to EO term. Resolves overloads, expands n-ary operators to binary form, handles binders and argument lists, expands defines. All semantic decisions are resolved here; output is plain EO terms with no LP-specific concerns.

**Encoding** (`encode.ml`): Elaborated EO terms are translated to LambdaPi `Core.Term` values. Key transformations include:
- **Overload resolution**: Multiple declarations of the same symbol (e.g., unary and binary `-`) are resolved by arity filtering and index-based LP symbol selection
- **Type lifting**: Eunoia types are lifted into LambdaPi via `tau : Set -> TYPE`
- **Placeholder resolution**: LambdaPi's type inference fills implicit arguments (`resolve.ml`)

The `Prelude.lp` file provides core Eunoia builtins (type universe, HOL application, boolean operators, arithmetic, list operations) as LambdaPi declarations and rewrite rules.

## CPC-MINI Coverage

CPC-MINI is a subset of cvc5's Cooperating Proof Calculus. eo2lp translates:

| Category | Modules |
|----------|---------|
| **Theories** | Builtin, Arith, Ints, Arrays, Sets, Quantifiers |
| **Rules** | Builtin, Booleans, Arith, Arrays, Uf, Sets, Quantifiers, Rewrites |
| **Programs** | Utils, Nary, Arith, AciNorm, DistinctValues, PolyNorm, Quantifiers |
| **Root** | Cpc |

All modules pass `lambdapi check` with full subject reduction verification.

## Project Structure

```
eo2lp/
  src/
    lexer.mll, parser.mly     Eunoia parser
    syntax_eo.ml               Eunoia AST and signature graphs
    parse_eo.ml                Parsing orchestration
    elaborate.ml               Eunoia elaboration (EO → EO)
    encode.ml                  Eunoia to LambdaPi translation
    lp_builders.ml             LP term construction helpers
    resolve.ml                 Type inference / placeholder resolution
    enc_numerals.ml            Numeric literal encoding
    api_lp.ml                  LambdaPi API wrapper and .lp output
    pp_eo.ml                   Eunoia pretty-printer
    literal.ml                 Literal type handling
    main.ml                    CLI driver
    eo2lp_cli.ml               Entry point
    Prelude.lp                 Core Eunoia builtins in LambdaPi
  test/
    test_parsing.ml            Parser unit tests
    test_encoding.ml           Prelude rewrite rule verification
    test_sig_graph.ml          Dependency graph tests
    test_util.ml               Shared test infrastructure
  scripts/
    bench.sh                   Parallel benchmark across fragments
    rerun-frag.sh              Re-run a single fragment
    sample-errors.sh           Sample errors from benchmark CSV
    diag.sh                    Diagnose a single proof
    gen-results-table.sh       Generate LaTeX table from CSV
    gen-proofs.sh              Generate proofs from SMT2 benchmarks
    setup-cpc.sh               Fetch CPC source from cvc5 fork
    diff-cpc.sh                Compare local CPC with upstream
  cpc/                         CPC-MINI source files (.eo)
  proofs/                      Proof benchmarks by SMT-LIB fragment
  tex/                         IJCAR paper sources
  _build/cpc/                  Generated LambdaPi package (.lp)
```

## License

This project is under development.
