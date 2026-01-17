# eo2lp

An OCaml tool for translating signatures and proof scripts from [Eunoia](https://github.com/cvc5/ethos/blob/main/user_manual.md) to [LambdaPi](https://github.com/Deducteam/lambdapi).

## Building

Build the project with dune:

```bash
dune build
```

## Usage

Translate a directory of Eunoia (`.eo`) files to LambdaPi:

```bash
dune exec eo2lp -- -d <input_dir> -o <output_dir>
```

Options:
- `-d <dir>` - Input directory containing `.eo` files (required)
- `-o <dir>` - Output directory for LambdaPi package (required)
- `-v` - Verbose output

Example:

```bash
dune exec eo2lp -- -d cpc-mini -o cpclp -v
```

This will:
1. Build a signature graph from all `.eo` files in `cpc-mini/`
2. Check for cycles in the dependency graph
3. Generate a LambdaPi package in `cpclp/` with:
   - `Prelude.lp` - Core Eunoia builtin symbols
   - `lambdapi.pkg` - Package configuration
   - One `.lp` file for each `.eo` file

### Generated File Structure

Each generated `.lp` file has the following import structure:

```lambdapi
require <package>.Prelude as eo;
require open Stdlib.Set Stdlib.HOL ... <dependencies>;
```

This allows Eunoia builtin symbols to be accessed via the `eo` namespace (e.g., `eo.ite`, `eo.eq`) while keeping Stdlib symbols in the global namespace.

## Testing

Run the test suite:

```bash
dune test
```

The test suite includes:
- **Parsing tests** - Verify `.eo` files parse correctly
- **Elaboration tests** - Test term elaboration and type inference
- **Encoding tests** - Test translation to LambdaPi
- **Graph tests** - Verify signature graph construction and topological sorting
- **Integration tests** - Full pipeline including optional LambdaPi checking

Run tests with custom timeout:

```bash
dune test -- -t 0.5  # 0.5 second timeout per test
```

Run tests in verbose mode:

```bash
dune test -- -v
```

## Project Structure

```
eo2lp/
├── src/           # Core library and CLI
│   ├── lexer.mll, parser.mly  # Eunoia parser
│   ├── syntax_eo.ml           # Eunoia AST and signature graphs
│   ├── elaborate.ml           # Term elaboration
│   ├── encode.ml              # Translation to LambdaPi
│   ├── syntax_lp.ml           # LambdaPi AST
│   ├── api_lp.ml              # LambdaPi file I/O
│   ├── main.ml                # CLI and package generation
│   └── eo2lp_cli.ml           # Entry point
├── test/          # Test suite
│   ├── test_infra.ml          # Shared test infrastructure
│   ├── test_core.ml           # Core.eo tests
│   ├── test_cpc_mini_*.ml     # CPC test suite
│   ├── test_graph.ml          # Graph algorithm tests
│   └── test_lp_check.ml       # LambdaPi integration tests
├── eo/            # Core Eunoia prelude
├── cpc-mini/      # Example: CPC proof calculus (miniature)
└── ethos-tests/   # Additional test files
```

## License

This repository is currently under construction.
