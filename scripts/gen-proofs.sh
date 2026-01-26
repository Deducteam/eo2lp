#!/bin/bash
# gen-proofs.sh
# Generate CPC proofs from SMT2 benchmark files using cvc5
#
# Usage:
#   ./scripts/gen-proofs.sh <input-dir> <output-dir> [timeout] [max-files]
#
# Example:
#   ./scripts/gen-proofs.sh ~/prog/smtlib/QF_UF/non-incremental/QF_UF/eq_diamond proofs/QF_UF/eq_diamond 10 100

set -e

INPUT_DIR="$1"
OUTPUT_DIR="$2"
TIMEOUT="${3:-10}"
MAX_FILES="${4:-0}"  # 0 means no limit

if [ -z "$INPUT_DIR" ] || [ -z "$OUTPUT_DIR" ]; then
    echo "Usage: $0 <input-dir> <output-dir> [timeout] [max-files]"
    exit 1
fi

if [ ! -d "$INPUT_DIR" ]; then
    echo "Error: Input directory '$INPUT_DIR' does not exist"
    exit 1
fi

mkdir -p "$OUTPUT_DIR"

count=0
success=0
failed=0

for smt2_file in "$INPUT_DIR"/*.smt2; do
    [ -f "$smt2_file" ] || continue

    if [ "$MAX_FILES" -gt 0 ] && [ "$count" -ge "$MAX_FILES" ]; then
        break
    fi

    basename=$(basename "$smt2_file" .smt2)
    output_file="$OUTPUT_DIR/$basename.eo"

    count=$((count + 1))

    # Run cvc5 with timeout, capture proof
    # - Strip first line ("unsat")
    # - Remove wrapping parens (first '(' and last ')')
    # - Add CPC includes at the top
    if timeout "$TIMEOUT" cvc5 --produce-proofs --dump-proofs "$smt2_file" 2>/dev/null | tail -n +2 | sed '1s/^(//' | sed '$s/)$//' > "$output_file.tmp"; then
        # Check if proof was actually generated (file has content)
        if grep -q "^(step\|^(assume" "$output_file.tmp" 2>/dev/null; then
            # Prepend comment and move to final location
            {
                echo "; Generated from $basename.smt2"
                echo ""
                cat "$output_file.tmp"
            } > "$output_file"
            rm -f "$output_file.tmp"
            success=$((success + 1))
            echo "[OK] $basename"
        else
            rm -f "$output_file" "$output_file.tmp"
            failed=$((failed + 1))
            echo "[SKIP] $basename (no proof - sat or unknown)"
        fi
    else
        rm -f "$output_file" "$output_file.tmp"
        failed=$((failed + 1))
        echo "[FAIL] $basename (timeout or error)"
    fi
done

echo ""
echo "Done: $success succeeded, $failed failed/skipped out of $count total"
echo "Proofs written to: $OUTPUT_DIR"
