# eo2lp

Translate proof signatures and scripts from [Eunoia](https://github.com/cvc5/ethos/blob/main/user_manual.md) (cvc5's proof language) to [LambdaPi](https://github.com/Deducteam/lambdapi).

Currently translates the full CPC (Co-operating Proof Calculus) -- 21 modules covering theories, inference rules, computational programs, and the main proof orchestration module -- with all generated files passing LambdaPi type checking including subject reduction verification.

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
- `--expert` -- Include files from `expert/` directory
- `--no-color` -- Disable colored output

### Example

```bash
# Translate CPC with error-level reporting
dune exec eo2lp -- -d cpc -o _build/cpc -v error

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
.eo files  -->  [Parse]  -->  Eunoia AST  -->  [Sig Graph]  -->  [Encode]  -->  .lp files
```

**Parsing**: A Menhir parser (`parser.mly`) and ocamllex tokenizer (`lexer.mll`) produce an Eunoia AST defined in `syntax_eo.ml`.

**Signature Graph**: Module dependencies are resolved from `include` directives. Cycles are detected and modules are topologically sorted.

**Encoding**: Each Eunoia symbol is translated directly to LambdaPi `Core.Term` values via `encode.ml`. Key transformations include:
- **N-ary expansion**: Operators with `:right-assoc-nil`, `:left-assoc`, `:chainable`, `:pairwise`, etc. are expanded to binary form
- **Overload resolution**: Multiple declarations of the same symbol (e.g., unary and binary `-`) are resolved by arity filtering and index-based LP symbol selection
- **`:arg-list` desugaring**: Operators like `distinct` that take argument lists have their arguments wrapped in list constructors
- **Binder encoding**: Quantifiers (`forall`, `exists`) with `:binder` attributes are encoded using variable-list constructors
- **Type lifting**: Eunoia types are lifted into LambdaPi via `tau : Set -> TYPE`

The `Prelude.lp` file provides ~420 lines of core Eunoia builtins (type universe, HOL application, boolean operators, arithmetic, list operations) as LambdaPi declarations and rewrite rules.

## CPC Coverage

The CPC (Co-operating Proof Calculus) defines cvc5's proof system. eo2lp currently translates:

| Category | Modules |
|----------|---------|
| **Theories** | Builtin, Arith, Ints, Arrays, Sets, Quantifiers |
| **Rules** | Builtin, Booleans, Arith, Arrays, Uf, Sets, Quantifiers, Rewrites |
| **Programs** | Utils, Nary, Arith, AciNorm, DistinctValues, Quantifiers |
| **Root** | Cpc |

All 21 modules pass `lambdapi check` with full subject reduction verification.

## Project Structure

```
eo2lp/
  src/
    lexer.mll, parser.mly     Eunoia parser
    syntax_eo.ml               Eunoia AST and signature graphs
    parse_eo.ml                Parsing orchestration
    encode.ml                  Eunoia to LambdaPi translation
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
    setup-cpc.sh               Fetch CPC source from cvc5 fork
    diff-cpc.sh                Compare local CPC with upstream
    gen-proofs.sh              Generate proofs from SMT2 benchmarks
  cpc -> (symlink)             CPC source files (.eo)
  _build/cpc/                  Generated LambdaPi package (.lp)
```

## License

This project is under development.
