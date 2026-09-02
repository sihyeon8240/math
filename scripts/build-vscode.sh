#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 2 ]]; then
  echo "usage: $0 <output-directory> <document> [latexmk-options...]" >&2
  exit 2
fi

out_dir="$1"
document="$2"
shift 2

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
document_dir="$(cd "$(dirname "$document")" && pwd)"
document_name="$(basename "$document")"

if [[ ! -f "$document_dir/$document_name" ]]; then
  echo "error: LaTeX document not found: $document" >&2
  exit 2
fi

mkdir -p "$out_dir"
while IFS= read -r -d '' source_dir; do
  relative="${source_dir#"$document_dir"/}"
  mkdir -p "$out_dir/$relative"
done < <(find "$document_dir" -mindepth 1 -type d -print0)

cd "$document_dir"
exec latexmk \
  -r "$repo_root/latexmkrc" \
  -outdir="$out_dir" \
  "$@" \
  "$document_name"
