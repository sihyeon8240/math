#!/usr/bin/env bash
set -u

output_file="${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}"
image_ref="${IMAGE_NAME:?IMAGE_NAME is required}:${RELEASE_TAG:?RELEASE_TAG is required}"

if docker manifest inspect "$image_ref" >/dev/null 2>&1; then
  echo "Immutable image tag already exists; it will not be overwritten." >&2
  echo "exists=true" >>"$output_file"
else
  echo "exists=false" >>"$output_file"
fi
