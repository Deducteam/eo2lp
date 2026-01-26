#!/bin/bash
# setup-cpc.sh
# Fetches and sets up CPC from the cvc5 repository (or your fork)
#
# Usage:
#   ./scripts/setup-cpc.sh                    # Use upstream cvc5
#   ./scripts/setup-cpc.sh your-username      # Use your fork
#   ./scripts/setup-cpc.sh your-username branch-name  # Use specific branch

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
CPC_DIR="$PROJECT_ROOT/cpc-source"

# Default to ciaran-matthew-dunne fork with cpc-fixes branch
GITHUB_USER="${1:-ciaran-matthew-dunne}"
BRANCH="${2:-cpc-fixes}"
REPO_URL="https://github.com/$GITHUB_USER/cvc5.git"

echo "Setting up CPC from $REPO_URL (branch: $BRANCH)"

# Check if cpc-source already exists
if [ -d "$CPC_DIR" ]; then
    echo "cpc-source already exists. Updating..."
    cd "$CPC_DIR"
    git fetch origin
    git checkout "$BRANCH"
    git pull origin "$BRANCH"
else
    echo "Cloning cvc5 repository (sparse checkout for proofs/eo/cpc only)..."

    # Use sparse checkout to only get the CPC directory
    git clone --filter=blob:none --sparse "$REPO_URL" "$CPC_DIR"
    cd "$CPC_DIR"
    git sparse-checkout set proofs/eo/cpc
    git checkout "$BRANCH"
fi

# Verify CPC files exist
if [ ! -d "$CPC_DIR/proofs/eo/cpc" ]; then
    echo "ERROR: CPC directory not found at $CPC_DIR/proofs/eo/cpc"
    exit 1
fi

echo ""
echo "CPC source set up successfully!"
echo "  Location: $CPC_DIR/proofs/eo/cpc"
echo ""
echo "Contents:"
ls -la "$CPC_DIR/proofs/eo/cpc"

# Create symlink for convenience
SYMLINK="$PROJECT_ROOT/cpc-upstream"
if [ -L "$SYMLINK" ]; then
    rm "$SYMLINK"
fi
ln -s "$CPC_DIR/proofs/eo/cpc" "$SYMLINK"
echo ""
echo "Created symlink: cpc-upstream -> cpc-source/proofs/eo/cpc"

echo ""
echo "To use this CPC source in a job file:"
echo "  (job"
echo "    (name my-job)"
echo "    (logic cpc-upstream)"
echo "    (proofs (dir path/to/proofs))"
echo "  )"
