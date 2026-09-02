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
eof_formatter="$repository_root/scripts/normalize-eof.sh"

if [[ "$mode" == "format" ]]; then
  echo "[py] formatting Python source files"
else
  echo "[py] checking Python source files"
fi

files=()
declare -A original_hashes=()
while IFS= read -r -d '' file; do
  [[ -f "$file" ]] || continue
  files+=("$file")
  original_hashes["$file"]="$(sha256sum "$file" | cut -d ' ' -f 1)"
done < <(
  git ls-files -z --cached --others --exclude-standard -- \
    'scripts/*.py' 'tests/*.py'
)

if [[ "$mode" == "check" ]]; then
  ruff format --check --quiet scripts tests
  ruff check --quiet scripts tests
  "$eof_formatter" --check "${files[@]}"
  echo "[py] ${#files[@]} files total: all correctly formatted"
else
  ruff check --fix --quiet scripts tests
  ruff format --quiet scripts tests
  "$eof_formatter" "${files[@]}"

  changed_count=0
  for file in "${files[@]}"; do
    formatted_hash="$(sha256sum "$file" | cut -d ' ' -f 1)"
    if [[ "$formatted_hash" != "${original_hashes[$file]}" ]]; then
      changed_count=$((changed_count + 1))
      echo "[py] reformatted: $file"
    fi
  done
  unchanged_count=$((${#files[@]} - changed_count))
  echo "[py] ${#files[@]} files total: $changed_count reformatted, $unchanged_count unchanged"
fi
