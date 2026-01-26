#!/bin/bash
# diff-cpc.sh
# Shows differences between cpc-mini (local modifications) and upstream CPC
#
# Usage:
#   ./scripts/diff-cpc.sh              # Show diff summary
#   ./scripts/diff-cpc.sh -v           # Show full diff

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

CPC_MINI="$PROJECT_ROOT/cpc-mini"
CPC_UPSTREAM="$PROJECT_ROOT/cpc-upstream"

if [ ! -d "$CPC_UPSTREAM" ]; then
    echo "ERROR: cpc-upstream not found. Run ./scripts/setup-cpc.sh first."
    exit 1
fi

if [ ! -d "$CPC_MINI" ]; then
    echo "ERROR: cpc-mini not found."
    exit 1
fi

echo "Comparing cpc-mini (local) with cpc-upstream..."
echo ""

# Directories to compare
DIRS="programs rules theories"

for dir in $DIRS; do
    MINI_DIR="$CPC_MINI/$dir"
    UPSTREAM_DIR="$CPC_UPSTREAM/$dir"

    if [ ! -d "$MINI_DIR" ]; then
        echo "[$dir] Not in cpc-mini"
        continue
    fi

    if [ ! -d "$UPSTREAM_DIR" ]; then
        echo "[$dir] Not in cpc-upstream"
        continue
    fi

    # Find files only in mini
    for f in "$MINI_DIR"/*.eo; do
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
        if [ ! -f "$MINI_DIR/$basename" ]; then
            echo "[$dir/$basename] UPSTREAM ONLY"
        fi
    done

    # Find modified files
    for f in "$MINI_DIR"/*.eo; do
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
if [ -f "$CPC_MINI/Cpc.eo" ]; then
    if [ -f "$CPC_UPSTREAM/Cpc.eo" ]; then
        if ! diff -q "$CPC_MINI/Cpc.eo" "$CPC_UPSTREAM/Cpc.eo" > /dev/null 2>&1; then
            echo "[Cpc.eo] MODIFIED"
        fi
    else
        echo "[Cpc.eo] LOCAL ONLY"
    fi
fi

echo ""
echo "Done. Use -v flag for detailed diffs."
