#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 0 ]]; then
  echo "usage: IMAGE=<tag> $0" >&2
  exit 2
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
image="${IMAGE:-math-toolchain:local}"

exec docker build --tag "$image" --file "$repo_root/.devcontainer/Dockerfile" "$repo_root"
