#!/bin/bash
# gen-proofs.sh - Generate CPC proofs from SMT2 files using cvc5
#
# Usage:
#   ./scripts/gen-proofs.sh <input-dir> <output-dir> [OPTIONS]
#
# Example:
#   ./scripts/gen-proofs.sh ~/prog/smtlib/QF_UF proofs/QF_UF
#   ./scripts/gen-proofs.sh ~/prog/smtlib/QF_UF proofs/QF_UF --timeout 5 --jobs 8 --max-lines 1000

set -euo pipefail
export LC_NUMERIC=C

INPUT_DIR=""
OUTPUT_DIR=""
TIMEOUT=10
JOBS=8
MAX_FILES=0

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

while [[ $# -gt 0 ]]; do
  case "$1" in
    --timeout)    TIMEOUT="$2"; shift 2 ;;
    --jobs)       JOBS="$2"; shift 2 ;;
    --max-files)  MAX_FILES="$2"; shift 2 ;;

    -h|--help)
      echo "Usage: $0 <input-dir> <output-dir> [OPTIONS]"
      echo ""
      echo "Options:"
      echo "  --timeout N     Seconds per cvc5 invocation (default: $TIMEOUT)"
      echo "  --jobs N        Parallel cvc5 jobs (default: $JOBS)"
      echo "  --max-files N   Max files to process, 0=all (default: $MAX_FILES)"
      exit 0
      ;;
    -*)
      echo "Unknown option: $1" >&2; exit 1 ;;
    *)
      if [[ -z "$INPUT_DIR" ]]; then
        INPUT_DIR="$1"
      elif [[ -z "$OUTPUT_DIR" ]]; then
        OUTPUT_DIR="$1"
      else
        echo "Unexpected argument: $1" >&2; exit 1
      fi
      shift
      ;;
  esac
done

if [[ -z "$INPUT_DIR" || -z "$OUTPUT_DIR" ]]; then
  echo "Usage: $0 <input-dir> <output-dir> [OPTIONS]" >&2
  exit 1
fi

if [[ ! -d "$INPUT_DIR" ]]; then
  echo "Error: input directory not found: $INPUT_DIR" >&2
  exit 1
fi

if ! command -v cvc5 &>/dev/null; then
  echo "Error: cvc5 not found in PATH" >&2
  exit 1
fi

mkdir -p "$OUTPUT_DIR"

# ---------------------------------------------------------------------------
# Worker function (called per .smt2 file via xargs)
# ---------------------------------------------------------------------------

process_one() {
  local smt2_file="$1"
  local output_dir="$2"
  local cvc5_timeout="$3"
  local bn
  bn=$(basename "$smt2_file" .smt2)
  local outfile="$output_dir/$bn.eo"
  local tmpfile="$outfile.tmp"

  if timeout "$cvc5_timeout" cvc5 --produce-proofs --dump-proofs \
       --proof-print-conclusion "$smt2_file" \
       > "$tmpfile" 2>/dev/null; then

    local first_line
    first_line=$(head -1 "$tmpfile")

    if [[ "$first_line" == "unsat" ]]; then
      tail -n +2 "$tmpfile" | sed '1s/^(//' | sed '$s/)$//' > "$outfile"

      if grep -qE '^\(step|^\(assume|^\(declare|^\(define' "$outfile" 2>/dev/null; then
        local lines
        lines=$(wc -l < "$outfile")

        echo "OK $bn (${lines} lines)"
      else
        rm -f "$outfile"
        echo "SKIP $bn (no proof content)"
      fi
    else
      rm -f "$outfile"
      echo "SKIP $bn ($first_line)"
    fi
  else
    local exit_code=$?
    rm -f "$outfile"
    if [[ $exit_code -eq 124 ]]; then
      echo "TIMEOUT $bn"
    else
      echo "FAIL $bn (exit $exit_code)"
    fi
  fi
  rm -f "$tmpfile"
}
export -f process_one

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

# Collect .smt2 files
filelist=$(mktemp)
find "$INPUT_DIR" -name '*.smt2' -type f | sort > "$filelist"
total=$(wc -l < "$filelist")

if [[ "$MAX_FILES" -gt 0 && "$total" -gt "$MAX_FILES" ]]; then
  head -n "$MAX_FILES" "$filelist" > "$filelist.tmp"
  mv "$filelist.tmp" "$filelist"
  total="$MAX_FILES"
fi

echo "Processing $total .smt2 files from $INPUT_DIR"
echo "  output: $OUTPUT_DIR"
echo "  timeout: ${TIMEOUT}s  jobs: $JOBS"
echo ""

# Run in parallel
results=$(mktemp)
cat "$filelist" | xargs -P"$JOBS" -I{} bash -c \
  'process_one "$@"' _ {} "$OUTPUT_DIR" "$TIMEOUT" \
  | tee "$results"

echo ""

# Summary
n_ok=$(grep -c '^OK ' "$results" || true)
n_skip=$(grep -c '^SKIP ' "$results" || true)
n_timeout=$(grep -c '^TIMEOUT ' "$results" || true)
n_fail=$(grep -c '^FAIL ' "$results" || true)
: "${n_ok:=0}" "${n_skip:=0}" "${n_timeout:=0}" "${n_fail:=0}"

n_proofs=$(find "$OUTPUT_DIR" -name '*.eo' -type f | wc -l)

echo "Done: $n_ok ok, $n_skip skip, $n_timeout timeout, $n_fail fail (out of $total)"
echo "Proofs: $n_proofs .eo files in $OUTPUT_DIR"

rm -f "$filelist" "$results"
