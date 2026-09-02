#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
PYTHON="${PYTHON:-python3}"
site_pages="$(mktemp -d)"
trap 'rm -rf -- "$site_pages"' EXIT
if ! command -v rg >/dev/null 2>&1; then
  echo "error: required command 'rg' (ripgrep) was not found in PATH" >&2
  exit 127
fi
if ! command -v shellcheck >/dev/null 2>&1; then
  echo "error: required command 'shellcheck' was not found in PATH" >&2
  exit 127
fi
bash -n scripts/*.sh
shellcheck --severity=error scripts/*.sh
"$PYTHON" scripts/books.py validate
"$PYTHON" scripts/generate-contents.py all --check
"$PYTHON" scripts/check-architecture.py
"$PYTHON" scripts/generate-site-pages.py --output-dir "$site_pages"
"$PYTHON" scripts/generate-site-pages.py --check --output-dir "$site_pages"
"$PYTHON" scripts/check-image-reference.py
"$PYTHON" scripts/check-proof-links.py

required=(
  Makefile
  pyproject.toml
  config/container-image.txt
  config/toolchain.env
  README.md
  docs/CONTRIBUTING.md
  scripts/format-python.sh
  scripts/format-shell.sh
  common/styles/textbook.sty
  common/styles/textbook-bibliography.sty
  common/styles/textbook-core.sty
  common/styles/textbook-math.sty
  common/styles/textbook-theorems.sty
  scripts/build-book.sh
  scripts/check-actions.sh
  scripts/check-lean.sh
  scripts/check-proof-links.py
  scripts/check-image-reference.py
  scripts/config_sync.py
  scripts/export-config.sh
  scripts/repository_config.py
  scripts/upload-release-assets.sh
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
echo "Repository source checks passed."
