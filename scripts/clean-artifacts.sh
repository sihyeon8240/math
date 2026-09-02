#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

case "$repo_root" in
/ | "")
  echo "error: refusing unsafe repository root" >&2
  exit 1
  ;;
esac

while IFS= read -r -d '' artifact; do
  rm -f -- "$artifact"
done < <(find "$repo_root" \
  -path "$repo_root/.git" -prune -o \
  -path "$repo_root/build" -prune -o \
  -path "$repo_root/vscode-build" -prune -o \
  -path "$repo_root/.latexindent_cache" -prune -o \
  -path "$repo_root/.ruff_cache" -prune -o \
  -path "$repo_root/lean/.lake" -prune -o \
  -type f \( \
  -name '*.aux' -o \
  -name '*.bbl' -o \
  -name '*.bcf' -o \
  -name '*.blg' -o \
  -name '*.fdb_latexmk' -o \
  -name '*.fls' -o \
  -name '*.idx' -o \
  -name '*.ilg' -o \
  -name '*.ind' -o \
  -name '*.lof' -o \
  -name '*.log' -o \
  -name '*.lot' -o \
  -name '*.out' -o \
  -name '*.pdf' -o \
  -name '*.run.xml' -o \
  -name '*.synctex.gz' -o \
  -name '*.toc' -o \
  -name '*.xdv' -o \
  -name '*.orig' -o \
  -name '*.rej' -o \
  -name '*.bak' -o \
  -name '*.backup' -o \
  -name '*.save' -o \
  -name '*.swp' -o \
  -name '*.swo' -o \
  -name '*~' -o \
  -name '.books.yml.*.tmp' \
  \) -print0)
