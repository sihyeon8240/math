#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
PYTHON="${PYTHON:-python3}"
if ! command -v rg >/dev/null 2>&1; then
  echo "error: required command 'rg' (ripgrep) was not found in PATH" >&2
  exit 127
fi
"$PYTHON" scripts/books.py validate
"$PYTHON" scripts/check-architecture.py
"$PYTHON" scripts/generate-readme-books.py --check
"$PYTHON" scripts/generate-site-pages.py --check
"$PYTHON" scripts/check-image-reference.py
"$PYTHON" scripts/check-proof-links.py

required=(
  Makefile
  pyproject.toml
  README.md
  docs/CONTRIBUTING.md
  scripts/format-python.sh
  common/styles/textbook.sty
  common/styles/textbook-core.sty
  common/styles/textbook-math.sty
  common/styles/textbook-theorems.sty
  common/styles/textbook-draft.sty
  common/templates/local-style.sty
  scripts/build-book.sh
  scripts/check-actions.sh
  scripts/check-lean.sh
  scripts/check-proof-links.py
  scripts/check-image-reference.py
  lean/lean-toolchain
  lean/lakefile.toml
  lean/Textbooks.lean
)
for path in "${required[@]}"; do
  if [[ ! -e "$path" ]]; then
    echo "error: required repository path is missing: $path" >&2
    exit 1
  fi
done

while IFS= read -r slug; do
  local_style="books/$slug/local-style.sty"
  if [[ ! -f "$local_style" ]]; then
    echo "error: registered book '$slug' is missing $local_style" >&2
    exit 1
  fi
  if ! rg -q -F '\usepackage{local-style}' "books/$slug/book.tex"; then
    echo "error: registered book '$slug' does not load local-style" >&2
    exit 1
  fi
done < <("$PYTHON" scripts/books.py list)

mapfile -t python_files < <(find scripts -type f -name '*.py' -print | sort)
if ((${#python_files[@]})); then
  "$PYTHON" -m py_compile "${python_files[@]}"
fi
mapfile -t tex_files < <(
  find books common/templates -type f -name '*.tex' -print 2>/dev/null | sort
)
"$PYTHON" scripts/check-labels.py "${tex_files[@]}"
if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  generated_directories='(^|/)(__pycache__|vscode-build|build|dist|\.lake'
  generated_directories+='|context.tex|tree.txt)/'
  generated_extensions='\.(aux|bbl|bcf|blg|fdb_latexmk|fls|idx'
  generated_extensions+='|ilg|ind|lof|log|lot|out|pdf|pyc'
  generated_extensions+='|run\.xml|synctex\.gz|toc|xdv)$'
  generated_pattern="$generated_directories|$generated_extensions"

  tracked_generated="$(git ls-files | grep -E "$generated_pattern" || true)"
  if [[ -n "$tracked_generated" ]]; then
    echo "error: generated files are tracked:" >&2
    printf '%s\n' "$tracked_generated" >&2
    exit 1
  fi
else
  echo "warning: Git metadata unavailable; skipped tracked generated-file check" >&2
fi
marker_pattern='TODO|VERIFY|SOURCECHECK|\\(todo|verify|sourcecheck)\{'
set +e
marker_output="$(rg -n "$marker_pattern" books --glob '*.tex')"
marker_status=$?
set -e
if ((marker_status > 1)); then
  echo "error: ripgrep failed while checking unfinished-writing markers" >&2
  exit "$marker_status"
fi
if [[ -n "$marker_output" ]]; then
  marker_count="$(printf '%s\n' "$marker_output" | wc -l | tr -d ' ')"
  echo "warning: found $marker_count unfinished-writing marker(s);" \
    "these are reported but do not fail CI" >&2
  printf '%s\n' "$marker_output" >&2
fi
echo "Repository source checks passed."
