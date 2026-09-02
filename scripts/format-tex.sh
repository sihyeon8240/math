#!/usr/bin/env bash
set -euo pipefail

mode="format"
if [[ "${1:-}" == "--check" ]]; then
  mode="check"
elif [[ $# -ne 0 ]]; then
  echo "usage: $0 [--check]" >&2
  exit 2
fi

if ! command -v latexindent >/dev/null 2>&1; then
  echo "error: latexindent is required" >&2
  exit 127
fi

repository_root="$(git rev-parse --show-toplevel)"
cd "$repository_root"
eof_formatter="$repository_root/scripts/normalize-eof.sh"

cruft_directory="$(mktemp -d)"
trap 'rm -rf "$cruft_directory"' EXIT

# A cached entry means that this exact file content has already passed the
# current formatter. Including the script and latexindent version in the cache
# namespace invalidates old results whenever the formatting rules or toolchain
# change.
cache_root="${FORMAT_TEX_CACHE_DIR:-$repository_root/.latexindent_cache}"
script_hash="$(sha256sum "$0" "$eof_formatter")"
latexindent_version="$(latexindent --version | head -n 1)"
cache_namespace="$(printf '%s\n%s\n' "$script_hash" "$latexindent_version" | sha256sum | cut -d ' ' -f 1)"
cache_directory="$cache_root/$cache_namespace"
mkdir -p "$cache_directory"

status=0
file_count=0
cached_count=0
changed_count=0
if [[ "$mode" == "format" ]]; then
  echo "[tex] formatting LaTeX source files"
else
  echo "[tex] checking LaTeX source files"
fi
while IFS= read -r -d '' file; do
  [[ -f "$file" ]] || continue
  file_count=$((file_count + 1))
  path_hash="$(printf '%s' "$file" | sha256sum | cut -d ' ' -f 1)"
  cache_entry="$cache_directory/$path_hash"
  content_hash="$(sha256sum "$file" | cut -d ' ' -f 1)"
  if [[ -f "$cache_entry" ]] && [[ "$(<"$cache_entry")" == "$content_hash" ]]; then
    cached_count=$((cached_count + 1))
    continue
  fi

  if [[ "$mode" == "check" ]]; then
    if ! latexindent \
      --check \
      --silent \
      --yaml="defaultIndent:'  '" \
      --cruft="$cruft_directory" \
      "$file"; then
      echo "[tex] needs formatting: $file" >&2
      status=1
      continue
    fi
    if ! "$eof_formatter" --check --collapse-blank-lines "$file"; then
      echo "[tex] needs formatting: $file" >&2
      status=1
      continue
    fi
  else
    latexindent \
      --overwriteIfDifferent \
      --silent \
      --yaml="defaultIndent:'  '" \
      --cruft="$cruft_directory" \
      "$file"
    "$eof_formatter" --collapse-blank-lines "$file"
    formatted_hash="$(sha256sum "$file" | cut -d ' ' -f 1)"
    if [[ "$formatted_hash" != "$content_hash" ]]; then
      changed_count=$((changed_count + 1))
      echo "[tex] reformatted: $file"
    fi
  fi
  sha256sum "$file" | cut -d ' ' -f 1 >"$cache_entry"
done < <(git ls-files -z --cached -- '*.tex' '*.sty')

if [[ "$status" -ne 0 ]]; then
  exit "$status"
fi

if [[ "$mode" == "format" ]]; then
  unchanged_count=$((file_count - cached_count - changed_count))
  echo "[tex] $file_count files total: $cached_count cached, $changed_count reformatted, $unchanged_count unchanged"
else
  echo "[tex] $file_count files checked, all correctly formatted ($cached_count cached)"
fi
