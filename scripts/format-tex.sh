#!/usr/bin/env bash
set -euo pipefail

mode="format"
if [[ $# -eq 1 && "$1" == "--check" ]]; then
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
format_settings="$repository_root/config/latexindent.yaml"

cruft_directory="$(mktemp -d)"
trap 'rm -rf "$cruft_directory"' EXIT

# Reuse checks only while the source, formatting rules, and tool version match.
cache_root="${FORMAT_TEX_CACHE_DIR:-$repository_root/.cache/latexindent}"
script_hash="$(sha256sum "$0" "$eof_formatter" "$format_settings")"
latexindent_version="$(latexindent --version | head -n 1)"
cache_namespace="$(printf '%s\n%s\n' "$script_hash" "$latexindent_version" | sha256sum | cut -d ' ' -f 1)"
cache_directory="$cache_root/$cache_namespace"
mkdir -p "$cache_directory"

# Preserve relative Lean indentation inside code-only environments.
normalize_lean_indentation() {
  perl -0777 -pe '
    s{^([\t ]*)(\\begin\{lean\}[\t ]*(?:%[^\n]*)?\n)(.*?)^[\t ]*(\\end\{lean\}[\t ]*(?:%[^\n]*)?$)}
     {
       my ($indent, $opening, $body, $closing) = ($1, $2, $3, $4);
       my $common;
       while ($body =~ /^([\t ]*)\S/gm) {
         my $prefix = $1;
         if (!defined $common) { $common = $prefix; }
         else {
           chop $common while length($common) && index($prefix, $common) != 0;
         }
       }
       if (defined $common) {
         $body =~ s/^\Q$common\E(?=[^\n]*\S)/$indent . "  "/gme;
       }
       $indent . $opening . $body . $indent . $closing;
     }gmse;
  ' "$1" >"$cruft_directory/lean-normalized.tex"
}

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

  wrapped_file="$cruft_directory/wrapped.${file##*.}"
  formatted_file="$cruft_directory/formatted.${file##*.}"
  latexindent \
    --modifylinebreaks \
    --local="$format_settings" \
    --cruft="$cruft_directory" \
    "$file" >"$wrapped_file"

  # latexindent 4.0.2 adds extra indentation to short wrapped sentences.
  # An indentation-only pass keeps the final result at the configured depth.
  latexindent \
    --local="$format_settings" \
    --cruft="$cruft_directory" \
    "$wrapped_file" >"$formatted_file"
  normalize_lean_indentation "$formatted_file"
  "$eof_formatter" --collapse-blank-lines "$cruft_directory/lean-normalized.tex"

  if ! cmp -s "$file" "$cruft_directory/lean-normalized.tex"; then
    if [[ "$mode" == "check" ]]; then
      echo "[tex] needs formatting: $file" >&2
      status=1
      continue
    fi
    cat "$cruft_directory/lean-normalized.tex" >"$file"
    changed_count=$((changed_count + 1))
    echo "[tex] reformatted: $file"
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
