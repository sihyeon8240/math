#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scope="${1:-}"

clean_directory() {
  local directory="$1"
  case "$directory" in
  "$repo_root/.cache/latexindent" | "$repo_root/.cache/ruff" | \
    "$repo_root/.cache/python" | "$repo_root/.cache/mathlib" | \
    "$repo_root/lean/.lake") ;;
  *)
    echo "error: refusing unsafe cache path" >&2
    exit 1
    ;;
  esac
  # Reject links at either level before traversing a default cache directory.
  if [[ -L "${directory%/*}" || -L "$directory" ]]; then
    echo "error: refusing symlinked cache path: $directory" >&2
    exit 1
  fi

  if [[ -d "$directory" ]]; then
    find "$directory" -mindepth 1 -delete
    rmdir "$directory"
  fi
}

case "$scope" in
lake)
  clean_directory "$repo_root/lean/.lake"
  ;;
mathlib)
  clean_directory "$repo_root/.cache/mathlib"
  ;;
tex)
  clean_directory "$repo_root/.cache/latexindent"
  ;;
ruff)
  clean_directory "$repo_root/.cache/ruff"
  ;;
py)
  clean_directory "$repo_root/.cache/python"
  ;;
all)
  clean_directory "$repo_root/.cache/mathlib"
  clean_directory "$repo_root/lean/.lake"
  clean_directory "$repo_root/.cache/latexindent"
  clean_directory "$repo_root/.cache/ruff"
  clean_directory "$repo_root/.cache/python"
  ;;
*)
  echo "usage: clean-cache.sh {lake|mathlib|tex|ruff|py|all}" >&2
  exit 2
  ;;
esac
