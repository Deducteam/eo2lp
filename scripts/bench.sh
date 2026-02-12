#!/bin/bash
# bench.sh - Parallel eo2lp benchmark across proof fragments
#
# Runs one eo2lp per fragment (subdirectory) in parallel, each with its own
# output directory. Merges per-fragment CSVs into a single results file.
#
# Usage:
#   ./scripts/bench.sh proofs/
#   ./scripts/bench.sh proofs/ --results bench_results.csv --timeout 5

set -euo pipefail
export LC_NUMERIC=C

# ---------------------------------------------------------------------------
# Defaults
# ---------------------------------------------------------------------------

PROOFS_DIR=""
RESULTS_FILE="bench_results.csv"
TIMEOUT=5
JOBS=0  # 0 = nproc

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"

# ---------------------------------------------------------------------------
# Argument parsing
# ---------------------------------------------------------------------------

print_usage() {
  cat <<EOF
Usage: $(basename "$0") [OPTIONS] <proofs-dir>

Parallel eo2lp benchmark across proof fragments.

Arguments:
  proofs-dir               Directory containing fragment subdirs of .eo files

Options:
  --results FILE           Output CSV file (default: $RESULTS_FILE)
  --timeout N              Per-proof timeout in seconds (default: $TIMEOUT)
  --jobs N                 Parallel jobs, 0=nproc (default: $JOBS)
  -h, --help               Show this help
EOF
}

while [[ $# -gt 0 ]]; do
  case "$1" in
    --results)  RESULTS_FILE="$2"; shift 2 ;;
    --timeout)  TIMEOUT="$2"; shift 2 ;;
    --jobs)     JOBS="$2"; shift 2 ;;
    -h|--help)  print_usage; exit 0 ;;
    -*)         echo "Unknown option: $1" >&2; print_usage; exit 1 ;;
    *)
      if [[ -z "$PROOFS_DIR" ]]; then
        PROOFS_DIR="$1"
      else
        echo "Unexpected argument: $1" >&2; print_usage; exit 1
      fi
      shift
      ;;
  esac
done

if [[ -z "$PROOFS_DIR" ]]; then
  echo "Error: specify a proofs directory" >&2
  print_usage
  exit 1
fi

PROOFS_DIR="$(cd "$PROOFS_DIR" && pwd)"

if [[ "$JOBS" -eq 0 ]]; then
  JOBS=$(nproc 2>/dev/null || echo 4)
fi

# ---------------------------------------------------------------------------
# Colors
# ---------------------------------------------------------------------------

if [[ -t 1 ]]; then
  RED=$'\033[31m'; GREEN=$'\033[32m'; YELLOW=$'\033[33m'
  DIM=$'\033[2m'; BOLD=$'\033[1m'; RESET=$'\033[0m'
else
  RED='' GREEN='' YELLOW='' DIM='' BOLD='' RESET=''
fi

# ---------------------------------------------------------------------------
# Discover fragments
# ---------------------------------------------------------------------------

fragments=()
for d in "$PROOFS_DIR"/*/; do
  [[ -d "$d" ]] || continue
  n=$(find "$d" -name '*.eo' -type f | wc -l)
  [[ "$n" -gt 0 ]] || continue
  fragments+=("$(basename "$d")")
done

n_frags=${#fragments[@]}
n_total=$(find "$PROOFS_DIR" -name '*.eo' -type f | wc -l)

if [[ "$n_frags" -eq 0 ]]; then
  echo "No fragments with .eo files found in $PROOFS_DIR" >&2
  exit 1
fi

# ---------------------------------------------------------------------------
# Build
# ---------------------------------------------------------------------------

echo -n "${DIM}building...${RESET} "
(cd "$PROJECT_DIR" && dune build 2>/dev/null)
EO2LP="$PROJECT_DIR/_build/default/src/eo2lp_cli.exe"
if [[ ! -x "$EO2LP" ]]; then
  echo "${RED}error: binary not found at $EO2LP${RESET}" >&2
  exit 1
fi
echo "${GREEN}ok${RESET}"
echo

echo "${BOLD}eo2lp bench${RESET}  ${DIM}$n_total proofs, $n_frags fragments, $JOBS jobs, ${TIMEOUT}s timeout${RESET}"
echo

# ---------------------------------------------------------------------------
# Working directory
# ---------------------------------------------------------------------------

WORK_DIR=$(mktemp -d)
trap 'rm -rf "$WORK_DIR"' EXIT

# ---------------------------------------------------------------------------
# Per-fragment worker
# ---------------------------------------------------------------------------

run_one() {
  local frag="$1"
  local frag_proofs="$PROOFS_DIR/$frag"
  local frag_out="$WORK_DIR/$frag/cpc"
  local frag_csv="$WORK_DIR/${frag}.csv"
  local n_proofs
  n_proofs=$(find "$frag_proofs" -name '*.eo' -type f | wc -l)

  mkdir -p "$frag_out"

  local t0 t1 elapsed_ms
  t0=$(date +%s%N)

  "$EO2LP" \
    -d "$PROJECT_DIR/cpc" \
    -o "$frag_out" \
    --proofs "$frag_proofs" \
    --check \
    --bench \
    --timeout "$TIMEOUT" \
    --results "$frag_csv" \
    --no-color \
    -v error \
    >/dev/null 2>"$WORK_DIR/${frag}.log" || true

  t1=$(date +%s%N)
  elapsed_ms=$(( (t1 - t0) / 1000000 ))
  local elapsed_s
  elapsed_s=$(awk "BEGIN{printf \"%.1f\", $elapsed_ms/1000}")

  # Count results
  local pass=0 enc_fail=0 chk_fail=0 timeout=0
  if [[ -f "$frag_csv" ]]; then
    pass=$(awk -F, 'NR>1 && $2=="pass"' "$frag_csv" | wc -l)
    enc_fail=$(awk -F, 'NR>1 && $2=="fail_encode"' "$frag_csv" | wc -l)
    chk_fail=$(awk -F, 'NR>1 && $2=="fail_check" && $5!="timeout"' "$frag_csv" | wc -l)
    timeout=$(awk -F, 'NR>1 && $5=="timeout"' "$frag_csv" | wc -l)
  fi

  local accounted=$(( pass + enc_fail + chk_fail + timeout ))
  local killed=""
  if [[ "$accounted" -lt "$n_proofs" ]]; then
    killed=" ${RED}(${n_proofs} - ${accounted} incomplete)${RESET}"
  fi

  # Format summary line
  local line
  line=$(printf "  %-16s %3d proofs  " "$frag" "$n_proofs")
  line+="${GREEN}${pass} pass${RESET}"
  [[ "$enc_fail" -gt 0 ]] && line+="  ${RED}${enc_fail} enc${RESET}"
  [[ "$chk_fail" -gt 0 ]] && line+="  ${RED}${chk_fail} chk${RESET}"
  [[ "$timeout"  -gt 0 ]] && line+="  ${YELLOW}${timeout} t/o${RESET}"
  line+="${killed}  ${DIM}${elapsed_s}s${RESET}"
  echo "$line" > "$WORK_DIR/${frag}.summary"
}
export -f run_one
export PROOFS_DIR WORK_DIR PROJECT_DIR TIMEOUT EO2LP
export RED GREEN YELLOW DIM BOLD RESET

# ---------------------------------------------------------------------------
# Run fragments in parallel
# ---------------------------------------------------------------------------

printf '%s\n' "${fragments[@]}" | xargs -P "$JOBS" -I{} bash -c 'run_one "$@"' _ {} &
xargs_pid=$!

# Progress: show per-proof and per-fragment counts, print fragment
# summaries as they complete
if [[ -t 1 ]]; then
  printed_frags=()
  while kill -0 "$xargs_pid" 2>/dev/null; do
    # Print any newly completed fragments (in order)
    for frag in "${fragments[@]}"; do
      already=false
      for p in "${printed_frags[@]}"; do
        [[ "$p" == "$frag" ]] && { already=true; break; }
      done
      if ! $already && [[ -f "$WORK_DIR/${frag}.summary" ]]; then
        printf "\r%60s\r" ""
        cat "$WORK_DIR/${frag}.summary"
        printed_frags+=("$frag")
      fi
    done

    # Count proofs done across all running fragments (each check line = 1 proof done)
    proofs_done=0
    frags_done=${#printed_frags[@]}
    for frag in "${fragments[@]}"; do
      if [[ -f "$WORK_DIR/${frag}.log" ]]; then
        c=$(grep -c "^BENCH.*check " "$WORK_DIR/${frag}.log" 2>/dev/null || true)
        proofs_done=$(( proofs_done + ${c:-0} ))
      fi
    done
    printf "\r  ${DIM}[%d/%d proofs] [%d/%d fragments]${RESET}   " \
      "$proofs_done" "$n_total" "$frags_done" "$n_frags"
    sleep 0.3
  done
  printf "\r%60s\r" ""
  # Print any remaining completed fragments
  for frag in "${fragments[@]}"; do
    already=false
    for p in "${printed_frags[@]}"; do
      [[ "$p" == "$frag" ]] && { already=true; break; }
    done
    if ! $already; then
      if [[ -f "$WORK_DIR/${frag}.summary" ]]; then
        cat "$WORK_DIR/${frag}.summary"
      else
        printf "  %-16s ${RED}no output${RESET}\n" "$frag"
      fi
    fi
  done
else
  wait "$xargs_pid" || true
  for frag in "${fragments[@]}"; do
    if [[ -f "$WORK_DIR/${frag}.summary" ]]; then
      cat "$WORK_DIR/${frag}.summary"
    else
      printf "  %-16s no output\n" "$frag"
    fi
  done
fi
wait "$xargs_pid" 2>/dev/null || true
echo

# ---------------------------------------------------------------------------
# Merge CSVs
# ---------------------------------------------------------------------------

echo "fragment,file,status,encode_time,check_time,error_category,error" > "$RESULTS_FILE"
for frag in "${fragments[@]}"; do
  frag_csv="$WORK_DIR/${frag}.csv"
  [[ -f "$frag_csv" ]] && tail -n +2 "$frag_csv" | sed "s/^/${frag},/" >> "$RESULTS_FILE"
done

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

n_results=$(( $(wc -l < "$RESULTS_FILE") - 1 ))
if [[ "$n_results" -eq 0 ]]; then
  echo "${YELLOW}No results.${RESET}"
  exit 0
fi

read -r total pass encfail chkfail tmo <<< "$(awk -F, '
  NR > 1 {
    total++
    if ($3 == "pass") pass++
    else if ($3 == "fail_encode") encfail++
    else if ($3 == "fail_check" && $6 == "timeout") tmo++
    else if ($3 == "fail_check") chkfail++
  }
  END { printf "%d %d %d %d %d", total, pass+0, encfail+0, chkfail+0, tmo+0 }
' "$RESULTS_FILE")"

pct=$(awk "BEGIN{printf \"%.1f\", ($pass/$total)*100}")

printf "${BOLD}%d${RESET}/${BOLD}%d${RESET} pass (%s%%)" "$pass" "$total" "$pct"
[[ "$encfail" -gt 0 ]] && printf "  ${RED}%d enc_fail${RESET}" "$encfail"
[[ "$chkfail" -gt 0 ]] && printf "  ${RED}%d chk_fail${RESET}" "$chkfail"
[[ "$tmo"     -gt 0 ]] && printf "  ${YELLOW}%d timeout${RESET}" "$tmo"
echo
echo

# Error category breakdown (if any errors)
if [[ $(( encfail + chkfail + tmo )) -gt 0 ]]; then
  echo "${BOLD}Errors by category:${RESET}"
  awk -F, 'NR > 1 && $6 != "" { cats[$6]++ }
    END { for (c in cats) printf "  %-24s %d\n", c, cats[c] }' "$RESULTS_FILE" | sort -t' ' -k2 -rn
  echo
fi

echo "${DIM}Results: $RESULTS_FILE${RESET}"
