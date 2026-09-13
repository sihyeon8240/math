#!/usr/bin/env bash
set -euo pipefail

base_revision="${1:?usage: check-dependabot-image-update.sh <base> [head]}"
head_revision="${2:-HEAD}"
allowed_paths='^\.devcontainer/Dockerfile$'

changed_paths="$(git diff --name-only "$base_revision" "$head_revision")"
if [[ -z "$changed_paths" ]] || grep -Evq "$allowed_paths" <<<"$changed_paths"; then
  echo "error: Dependabot image PR contains an unexpected changed file" >&2
  exit 1
fi

dockerfile_diff="$(
  git diff --unified=0 "$base_revision" "$head_revision" -- .devcontainer/Dockerfile |
    sed -n '/^[+-][^+-]/p'
)"
if [[ -z "$dockerfile_diff" ]] || grep -Evq '^[+-][[:space:]]*FROM[[:space:]]' <<<"$dockerfile_diff"; then
  echo "error: Dependabot Dockerfile update must change only FROM lines" >&2
  exit 1
fi
