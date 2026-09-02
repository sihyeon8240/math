#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

"$repo_root/scripts/check-repository.sh"
"$repo_root/scripts/format-python.sh" --check
"$repo_root/scripts/format-shell.sh" --check
"$repo_root/scripts/format-tex.sh" --check
"$repo_root/scripts/normalize-eof.sh" --check
"$repo_root/scripts/check-lean.sh"
BOOKS_MANIFEST_VALIDATED=1 "$repo_root/scripts/build-all.sh" check
