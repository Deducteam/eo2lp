#!/bin/bash
# diff-cpc.sh
# Shows differences between cpc/ (local submodule) and upstream CPC from cvc5
#
# Usage:
#   ./scripts/diff-cpc.sh              # Show diff summary
#   ./scripts/diff-cpc.sh -v           # Show full diff

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

CPC_LOCAL="$PROJECT_ROOT/cpc"
CPC_UPSTREAM_REPO="$PROJECT_ROOT/cpc-upstream-repo"
CPC_UPSTREAM="$CPC_UPSTREAM_REPO/proofs/eo/cpc"

if [ ! -d "$CPC_LOCAL" ]; then
    echo "ERROR: cpc/ submodule not found. Run 'git submodule update --init'."
    exit 1
fi

# Fetch upstream if not present
if [ ! -d "$CPC_UPSTREAM" ]; then
    echo "Fetching upstream CPC from cvc5..."
    git clone --filter=blob:none --sparse \
        https://github.com/cvc5/cvc5.git "$CPC_UPSTREAM_REPO"
    cd "$CPC_UPSTREAM_REPO"
    git sparse-checkout set proofs/eo/cpc
    cd "$PROJECT_ROOT"
    echo ""
fi

echo "Comparing cpc/ (local) with upstream cvc5 CPC..."
echo ""

# Directories to compare
DIRS="programs rules theories"

for dir in $DIRS; do
    LOCAL_DIR="$CPC_LOCAL/$dir"
    UPSTREAM_DIR="$CPC_UPSTREAM/$dir"

    if [ ! -d "$LOCAL_DIR" ]; then
        echo "[$dir] Not in cpc/"
        continue
    fi

    if [ ! -d "$UPSTREAM_DIR" ]; then
        echo "[$dir] Not in upstream"
        continue
    fi

    # Find files only in local
    for f in "$LOCAL_DIR"/*.eo; do
        [ -f "$f" ] || continue
        basename=$(basename "$f")
        if [ ! -f "$UPSTREAM_DIR/$basename" ]; then
            echo "[$dir/$basename] LOCAL ONLY"
        fi
    done

    # Find files only in upstream
    for f in "$UPSTREAM_DIR"/*.eo; do
        [ -f "$f" ] || continue
        basename=$(basename "$f")
        if [ ! -f "$LOCAL_DIR/$basename" ]; then
            echo "[$dir/$basename] UPSTREAM ONLY"
        fi
    done

    # Find modified files
    for f in "$LOCAL_DIR"/*.eo; do
        [ -f "$f" ] || continue
        basename=$(basename "$f")
        if [ -f "$UPSTREAM_DIR/$basename" ]; then
            if ! diff -q "$f" "$UPSTREAM_DIR/$basename" > /dev/null 2>&1; then
                echo "[$dir/$basename] MODIFIED"
                if [ "$1" = "-v" ]; then
                    echo "---"
                    diff -u "$UPSTREAM_DIR/$basename" "$f" | head -50
                    echo "---"
                fi
            fi
        fi
    done
done

# Check Cpc.eo
if [ -f "$CPC_LOCAL/Cpc.eo" ]; then
    if [ -f "$CPC_UPSTREAM/Cpc.eo" ]; then
        if ! diff -q "$CPC_LOCAL/Cpc.eo" "$CPC_UPSTREAM/Cpc.eo" > /dev/null 2>&1; then
            echo "[Cpc.eo] MODIFIED"
        fi
    else
        echo "[Cpc.eo] LOCAL ONLY"
    fi
fi

echo ""
echo "Done. Use -v flag for detailed diffs."
