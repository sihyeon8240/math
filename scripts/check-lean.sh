#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON="${PYTHON:-python3}"

if ! command -v lake >/dev/null 2>&1; then
  echo "error: required command 'lake' was not found in PATH" >&2
  echo "Install the pinned toolchain from lean/lean-toolchain with elan." >&2
  exit 127
fi

if rg -n '\b(sorry|admit)\b|^[[:space:]]*axiom[[:space:]]' \
  "$repo_root/lean/Textbooks" --glob '*.lean'; then
  echo "error: unchecked Lean proof escape hatch found" >&2
  exit 1
fi

cd "$repo_root/lean"
lake build
cd "$repo_root"
"$PYTHON" scripts/check-proof-links.py --check-declarations
