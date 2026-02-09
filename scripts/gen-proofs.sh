#!/bin/bash
# gen-proofs.sh - Find unsat SMT2 problems and optionally generate CPC proofs
#
# Modes:
#   Default:    Copy unsat .smt2 files to output directory
#   --proofs:   Generate .eo proof files from unsat problems via cvc5
#
# Usage:
#   ./scripts/gen-proofs.sh <input-dir> <output-dir> [OPTIONS]
#
# The input-dir can be either:
#   - A single directory of .smt2 files (processed directly)
#   - A directory of fragment subdirs (e.g. QF_UF/, QF_LIA/), each processed
#
# Examples:
#   # Sample 10 unsat problems per fragment
#   ./scripts/gen-proofs.sh ~/prog/smtlib samples -n 10
#
#   # Generate proofs from a single fragment
#   ./scripts/gen-proofs.sh ~/prog/smtlib/QF_UF proofs/QF_UF --proofs
#
#   # Generate proofs from all fragments, 20 per fragment
#   ./scripts/gen-proofs.sh ~/prog/smtlib proofs --proofs -n 20 --timeout 5

set -euo pipefail
export LC_NUMERIC=C

INPUT_DIR=""
OUTPUT_DIR=""
TIMEOUT=10
MAX_FILES=0
MAX_LINES=0
JOBS=0
PROOFS=false
SHUFFLE=false

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

print_usage() {
  cat <<EOF
Usage: $(basename "$0") <input-dir> <output-dir> [OPTIONS]

Find unsat SMT2 problems and optionally generate CPC proofs.

Arguments:
  input-dir     Directory of .smt2 files, or parent of fragment subdirs
  output-dir    Output directory

Options:
  --proofs        Generate .eo proof files (default: copy .smt2 files)
  --shuffle       Randomize file order (default when -n is set)
  -n N            Stop after N unsat problems per directory (default: 0=all)
  --max-lines N   Discard .eo proofs exceeding N lines (default: 0=no limit)
  --timeout N     Seconds per cvc5 invocation (default: $TIMEOUT)
  --jobs N        Parallel jobs for multi-fragment, 0=nproc (default: $JOBS)
  -h, --help      Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --proofs)     PROOFS=true; shift ;;
    --shuffle)    SHUFFLE=true; shift ;;
    -n)           MAX_FILES="$2"; SHUFFLE=true; shift 2 ;;
    --max-lines)  MAX_LINES="$2"; shift 2 ;;
    --timeout)    TIMEOUT="$2"; shift 2 ;;
    --jobs)       JOBS="$2"; shift 2 ;;
    -h|--help)    print_usage; exit 0 ;;
    -*)           echo "Unknown option: $1" >&2; print_usage; exit 1 ;;
    *)
      if [[ -z "$INPUT_DIR" ]]; then
        INPUT_DIR="$1"
      elif [[ -z "$OUTPUT_DIR" ]]; then
        OUTPUT_DIR="$1"
      else
        echo "Unexpected argument: $1" >&2; print_usage; exit 1
      fi
      shift
      ;;
  esac
done

if [[ -z "$INPUT_DIR" || -z "$OUTPUT_DIR" ]]; then
  print_usage >&2; exit 1
fi

if [[ ! -d "$INPUT_DIR" ]]; then
  echo "Error: input directory not found: $INPUT_DIR" >&2; exit 1
fi

if ! command -v cvc5 &>/dev/null; then
  echo "Error: cvc5 not found in PATH" >&2; exit 1
fi

if [[ "$JOBS" -eq 0 ]]; then
  JOBS=$(nproc 2>/dev/null || echo 4)
fi

# ---------------------------------------------------------------------------
# Process one directory of .smt2 files
# ---------------------------------------------------------------------------

process_dir() {
  local in_dir="$1" out_dir="$2"
  local frag
  frag=$(basename "$in_dir")
  mkdir -p "$out_dir"

  # Collect .smt2 files
  local filelist
  filelist=$(mktemp)
  if [[ "$SHUFFLE" == true ]]; then
    find -L "$in_dir" -name '*.smt2' -type f | shuf > "$filelist"
  else
    find -L "$in_dir" -name '*.smt2' -type f | sort > "$filelist"
  fi
  local total
  total=$(wc -l < "$filelist")

  local n=0 ok=0 sat=0 unk=0 tmout=0 fail=0

  while IFS= read -r smt2_file; do
    # Stop early if we have enough
    if [[ "$MAX_FILES" -gt 0 && "$ok" -ge "$MAX_FILES" ]]; then
      break
    fi

    local bn
    bn=$(basename "$smt2_file" .smt2)

    if [[ "$PROOFS" == true ]]; then
      # Generate proof mode: run cvc5 with proof options, extract .eo
      local outfile="$out_dir/$bn.eo"
      local tmpfile="$outfile.tmp"

      if timeout "$TIMEOUT" cvc5 --produce-proofs --dump-proofs \
           --proof-granularity=dsl-rewrite \
           --proof-print-conclusion "$smt2_file" \
           > "$tmpfile" 2>/dev/null; then

        local first_line
        first_line=$(head -1 "$tmpfile")

        if [[ "$first_line" == "unsat" ]]; then
          tail -n +2 "$tmpfile" | sed '1s/^(//' | sed '$s/)$//' > "$outfile"

          if grep -qE '^\(step|^\(assume|^\(declare|^\(define' "$outfile" 2>/dev/null; then
            if [[ "$MAX_LINES" -gt 0 ]] && [[ $(wc -l < "$outfile") -gt "$MAX_LINES" ]]; then
              rm -f "$outfile"
            else
              ok=$((ok + 1))
            fi
          else
            rm -f "$outfile"
          fi
        elif [[ "$first_line" == "sat" ]]; then
          sat=$((sat + 1))
        elif [[ "$first_line" == "unknown" ]]; then
          unk=$((unk + 1))
        fi
        rm -f "$tmpfile"
      else
        local exit_code=$?
        rm -f "$tmpfile"
        if [[ $exit_code -eq 124 ]]; then
          tmout=$((tmout + 1))
        else
          fail=$((fail + 1))
        fi
      fi
    else
      # Sample mode: check sat/unsat, copy .smt2 if unsat
      local result
      result=$(timeout "$TIMEOUT" cvc5 "$smt2_file" 2>/dev/null | head -1) || true

      if [[ "$result" == "unsat" ]]; then
        cp "$smt2_file" "$out_dir/"
        ok=$((ok + 1))
      elif [[ "$result" == "sat" ]]; then
        sat=$((sat + 1))
      elif [[ "$result" == "unknown" ]]; then
        unk=$((unk + 1))
      else
        fail=$((fail + 1))
      fi
    fi

    n=$((n + 1))

    # Progress (only in single-dir / non-parallel mode)
    if [[ "$PARALLEL" != true ]]; then
      printf "\r  [%d/%d] %d unsat, %d sat, %d unknown, %d timeout, %d fail" \
        "$n" "$total" "$ok" "$sat" "$unk" "$tmout" "$fail"
    fi
  done < "$filelist"

  rm -f "$filelist"

  if [[ "$PARALLEL" == true ]]; then
    printf "  %-14s %d unsat (tried %d/%d)\n" "$frag" "$ok" "$n" "$total"
  else
    printf "\r  [%d/%d] %d unsat, %d sat, %d unknown, %d timeout, %d fail\n" \
      "$n" "$total" "$ok" "$sat" "$unk" "$tmout" "$fail"
  fi
}

# ---------------------------------------------------------------------------
# Main: detect single-dir vs multi-fragment
# ---------------------------------------------------------------------------

# Check if input-dir contains .smt2 files directly
has_smt2=$(find -L "$INPUT_DIR" -maxdepth 1 -name '*.smt2' -type f | head -1)

# Check if input-dir has subdirectories
has_subdirs=false
for d in "$INPUT_DIR"/*/; do
  if [[ -d "$d" ]]; then
    has_subdirs=true
    break
  fi
done

if [[ -n "$has_smt2" ]] || [[ "$has_subdirs" == false ]]; then
  # Single directory mode
  PARALLEL=false
  export PARALLEL
  frag=$(basename "$INPUT_DIR")
  total=$(find -L "$INPUT_DIR" -name '*.smt2' -type f | wc -l)
  echo "$frag: $total problems, timeout ${TIMEOUT}s"
  process_dir "$INPUT_DIR" "$OUTPUT_DIR"

  if [[ "$PROOFS" == true ]]; then
    n_out=$(find "$OUTPUT_DIR" -name '*.eo' -type f | wc -l)
    echo "  $n_out proofs in $OUTPUT_DIR"
  else
    n_out=$(find "$OUTPUT_DIR" -name '*.smt2' -type f | wc -l)
    echo "  $n_out problems in $OUTPUT_DIR"
  fi
else
  # Multi-fragment mode
  PARALLEL=true
  export PARALLEL

  fragments=()
  for d in "$INPUT_DIR"/*/; do
    [[ -d "$d" ]] || continue
    fragments+=("$(basename "$d")")
  done

  label="proofs"
  [[ "$PROOFS" == true ]] || label="unsat problems"
  limit_msg=""
  [[ "$MAX_FILES" -eq 0 ]] || limit_msg=", max $MAX_FILES per fragment"
  echo "Gathering ${label} from ${#fragments[@]} fragments (timeout ${TIMEOUT}s, $JOBS jobs${limit_msg})"
  echo

  export -f process_dir
  export INPUT_DIR OUTPUT_DIR TIMEOUT MAX_FILES MAX_LINES PROOFS SHUFFLE

  printf '%s\n' "${fragments[@]}" | xargs -P "$JOBS" -I{} \
    bash -c 'process_dir "$INPUT_DIR/{}" "$OUTPUT_DIR/{}"' _

  echo
  if [[ "$PROOFS" == true ]]; then
    total=$(find "$OUTPUT_DIR" -name '*.eo' -type f | wc -l)
    echo "Total: $total proofs in $OUTPUT_DIR"
  else
    total=$(find "$OUTPUT_DIR" -name '*.smt2' -type f | wc -l)
    echo "Total: $total problems in $OUTPUT_DIR"
  fi
fi
