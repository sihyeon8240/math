#!/usr/bin/env bash
set -euo pipefail

mode="format"
if [[ "${1:-}" == "--check" ]]; then
  mode="check"
elif [[ $# -ne 0 ]]; then
  echo "usage: $0 [--check]" >&2
  exit 2
fi

if ! command -v ruff >/dev/null 2>&1; then
  echo "error: ruff is required" >&2
  exit 127
fi

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"

if [[ "$mode" == "format" ]]; then
  echo "[py] formatting Python source files"
else
  echo "[py] checking Python source files"
fi

files=()
declare -A original_hashes=()
while IFS= read -r -d '' file; do
  files+=("$file")
  original_hashes["$file"]="$(sha256sum "$file" | cut -d ' ' -f 1)"
done < <(git ls-files -z 'scripts/*.py' 'tests/*.py')

if [[ "$mode" == "check" ]]; then
  ruff format --check --quiet scripts tests
  ruff check --quiet scripts tests
  echo "[py] ${#files[@]} files checked, all correctly formatted"
else
  ruff check --fix --quiet scripts tests
  ruff format --quiet scripts tests

  changed_count=0
  for file in "${files[@]}"; do
    formatted_hash="$(sha256sum "$file" | cut -d ' ' -f 1)"
    if [[ "$formatted_hash" != "${original_hashes[$file]}" ]]; then
      changed_count=$((changed_count + 1))
      echo "[py] reformatted: $file"
    fi
  done
  echo "[py] ${#files[@]} files checked, $changed_count reformatted"
fi

