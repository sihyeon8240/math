#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON="${PYTHON:-python3}"
export PYTHONPYCACHEPREFIX="${PYTHONPYCACHEPREFIX:-$repo_root/.cache/python}"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$repo_root/.cache/mathlib}"

if ! command -v lake >/dev/null 2>&1; then
  echo "error: required command 'lake' was not found in PATH" >&2
  echo "Install the pinned toolchain from lean/lean-toolchain with elan." >&2
  exit 127
fi

cd "$repo_root/lean"
lake build
cd "$repo_root"
"$PYTHON" scripts/check-proof-links.py --check-declarations
