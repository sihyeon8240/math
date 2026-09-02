#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scope="${1:-}"

clean_directory() {
  local directory="$1"
  case "$directory" in
  "$repo_root/lean/.lake" | "$repo_root/.latexindent_cache" | "$repo_root/.ruff_cache") ;;
  *)
    echo "error: refusing unsafe cache path" >&2
    exit 1
    ;;
  esac
  if [[ -d "$directory" ]]; then
    find "$directory" -mindepth 1 -delete
    rmdir "$directory"
  fi
}

clean_python() {
  while IFS= read -r -d '' bytecode; do
    rm -f -- "$bytecode"
  done < <(find "$repo_root" \
    -path "$repo_root/.git" -prune -o \
    -type f -name '*.pyc' -print0)
  while IFS= read -r -d '' cache; do
    find "$cache" -mindepth 1 -delete
    rmdir "$cache"
  done < <(find "$repo_root" \
    -path "$repo_root/.git" -prune -o \
    -type d -name '__pycache__' -print0)
}

case "$scope" in
lake)
  clean_directory "$repo_root/lean/.lake"
  ;;
tex)
  clean_directory "$repo_root/.latexindent_cache"
  ;;
ruff)
  clean_directory "$repo_root/.ruff_cache"
  ;;
py)
  clean_python
  ;;
all)
  clean_directory "$repo_root/lean/.lake"
  clean_directory "$repo_root/.latexindent_cache"
  clean_directory "$repo_root/.ruff_cache"
  clean_python
  ;;
*)
  echo "usage: clean-cache.sh {lake|tex|ruff|py|all}" >&2
  exit 2
  ;;
esac
