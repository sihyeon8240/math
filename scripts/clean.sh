#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
build_dir="$repo_root/build"
vscode_build_dir="$repo_root/vscode-build"

for directory in "$build_dir" "$vscode_build_dir"; do
  case "$directory" in
  "$repo_root/build" | "$repo_root/vscode-build") ;;
  *)
    echo "error: refusing unsafe clean paths" >&2
    exit 1
    ;;
  esac

  mkdir -p "$directory"
  find "$directory" -mindepth 1 -delete
done
