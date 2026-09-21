#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 0 ]]; then
  echo "usage: IMAGE=<ref> CMD=<command> $0" >&2
  exit 2
fi

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
image="${IMAGE:-}"
if [[ -z "$image" ]]; then
  IFS= read -r image <"$repo_root/config/container-image.txt"
fi
if [[ -z "$image" ]]; then
  echo "error: the container image reference is empty" >&2
  exit 2
fi

# Keep the writable home outside build output so cleaning does not erase caches.
repository_id="$(printf '%s' "$repo_root" | cksum | cut -d ' ' -f 1)"
container_home="${XDG_CACHE_HOME:-${HOME}/.cache}/math-container/$repository_id"
mkdir -p "$container_home"

arguments=(
  run --rm --init --interactive
  --user "$(id -u):$(id -g)"
  --volume "$repo_root:/workspace"
  --volume "$container_home:/home/developer"
  --workdir /workspace
  --env HOME=/home/developer
  --env ELAN_HOME=/home/developer/.elan
  --entrypoint /workspace/scripts/container-entrypoint.sh
  --env "TERM=${TERM:-xterm-256color}"
  --env 'TEXINPUTS=.:/workspace/common/styles//:/workspace/common/templates//:'
)
if [[ -t 0 && -t 1 ]]; then
  arguments+=(--tty)
fi

if [[ -n "${CMD:-}" ]]; then
  exec docker "${arguments[@]}" "$image" /bin/bash -c "$CMD"
fi
exec docker "${arguments[@]}" "$image" /bin/zsh
