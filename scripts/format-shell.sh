#!/usr/bin/env bash
set -euo pipefail

mode="format"
if [[ "${1:-}" == "--check" ]]; then
  mode="check"
elif [[ $# -ne 0 ]]; then
  echo "usage: $0 [--check]" >&2
  exit 2
fi

if ! command -v shfmt >/dev/null 2>&1; then
  echo "error: shfmt is required" >&2
  exit 127
fi

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"
eof_formatter="$repository_root/scripts/normalize-eof.sh"

files=()
declare -A original_hashes=()
while IFS= read -r -d '' file; do
  [[ -f "$file" ]] || continue
  files+=("$file")
  original_hashes["$file"]="$(sha256sum "$file" | cut -d ' ' -f 1)"
done < <(
  git ls-files -z --cached --others --exclude-standard -- 'scripts/*.sh'
)

if [[ "$mode" == "check" ]]; then
  echo "[sh] checking shell source files"
  shfmt -d -ln bash -i 2 "${files[@]}"
  "$eof_formatter" --check "${files[@]}"
  echo "[sh] ${#files[@]} files total: all correctly formatted"
else
  echo "[sh] formatting shell source files"
  shfmt -w -ln bash -i 2 "${files[@]}"
  "$eof_formatter" "${files[@]}"

  changed_count=0
  for file in "${files[@]}"; do
    formatted_hash="$(sha256sum "$file" | cut -d ' ' -f 1)"
    if [[ "$formatted_hash" != "${original_hashes[$file]}" ]]; then
      changed_count=$((changed_count + 1))
      echo "[sh] reformatted: $file"
    fi
  done
  unchanged_count=$((${#files[@]} - changed_count))
  echo "[sh] ${#files[@]} files total: $changed_count reformatted, $unchanged_count unchanged"
fi
