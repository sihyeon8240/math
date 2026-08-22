#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <slug> \"<title>\"" >&2
  exit 2
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
PYTHON="${PYTHON:-python3}"
slug="$1"
title="$2"

"$PYTHON" "$repo_root/scripts/books.py" validate-new "$slug" "$title"

target="$repo_root/books/$slug"

if [[ -e "$target" ]]; then
  echo "error: refusing to overwrite existing path: $target" >&2
  exit 1
fi

"$PYTHON" "$repo_root/scripts/books.py" validate
manifest_backup="$(mktemp /tmp/math-books-manifest.XXXXXX)"
cp "$repo_root/books.yml" "$manifest_backup"
cleanup() {
  cp "$manifest_backup" "$repo_root/books.yml"
  rm -f "$manifest_backup"
  if [[ -d "$target" ]]; then
    echo "error: creation failed; removing $target" >&2
    rm -rf "$target"
  fi
}

trap cleanup ERR

mkdir -p "$target/chapters/01-introduction" "$target/frontmatter"

cp \
  "$repo_root/common/templates/book.tex" \
  "$target/book.tex"

cp \
  "$repo_root/common/templates/metadata.tex" \
  "$target/metadata.tex"

cp \
  "$repo_root/common/templates/README.md" \
  "$target/README.md"

cp \
  "$repo_root/common/templates/chapter.tex" \
  "$target/chapters/01-introduction/index.tex"

cp \
  "$repo_root/common/templates/section.tex" \
  "$target/chapters/01-introduction/01-first-section.tex"

cp \
  "$repo_root/common/templates/local-style.sty" \
  "$target/local-style.sty"

cp \
  "$repo_root/common/templates/references.bib" \
  "$target/references.bib"

cp \
  "$repo_root/common/templates/frontmatter/title-and-copyright.tex" \
  "$target/frontmatter/title-and-copyright.tex"

cp \
  "$repo_root/common/templates/frontmatter/preface.tex" \
  "$target/frontmatter/preface.tex"

TITLE="$title" SLUG="$slug" perl -pi -e \
  's/__TITLE__/$ENV{TITLE}/g; s/__SLUG__/$ENV{SLUG}/g; s/__BOOK_TITLE__/$ENV{TITLE}/g; s/__BOOK_SLUG__/$ENV{SLUG}/g' \
  "$target/metadata.tex" \
  "$target/README.md"

"$PYTHON" "$repo_root/scripts/books.py" add "$slug" "$title"
label_prefix="$("$PYTHON" "$repo_root/scripts/books.py" label-prefix "$slug")"
LABEL_PREFIX="$label_prefix" perl -pi -e 's/xx:/$ENV{LABEL_PREFIX}:/g' \
  "$target/chapters/01-introduction/index.tex" \
  "$target/chapters/01-introduction/01-first-section.tex"
"$PYTHON" "$repo_root/scripts/generate-readme-books.py" --books --book "$slug"
rm -f "$manifest_backup"
trap - ERR

echo "Created books/$slug"
echo "Registered '$slug' in books.yml as draft"
echo "Site publication remains disabled; see docs/site-metadata.md to enable it"
