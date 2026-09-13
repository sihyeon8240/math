#!/usr/bin/env bash
set -euo pipefail

output_file="${GITHUB_OUTPUT:?GITHUB_OUTPUT is required}"
image_ref="${IMAGE_REF:-${IMAGE_NAME:?IMAGE_NAME is required}:${RELEASE_TAG:?RELEASE_TAG is required}}"

if manifest="$(docker manifest inspect "$image_ref")"; then
  if ! printf '%s' "$manifest" | python3 -c '
import json
import sys

manifest = json.load(sys.stdin)
platforms = {
    (entry.get("platform", {}).get("os"), entry.get("platform", {}).get("architecture"))
    for entry in manifest.get("manifests", [])
}
sys.exit(not {("linux", "amd64"), ("linux", "arm64")} <= platforms)
'; then
    echo "error: existing image lacks the required AMD64/ARM64 index: $image_ref" >&2
    echo "Bump the image build policy version; immutable tags must not be overwritten." >&2
    exit 1
  fi
  echo "Immutable multi-platform image exists; it will not be overwritten." >&2
  echo "exists=true" >>"$output_file"
else
  if [[ "${REQUIRE_IMAGE:-false}" == true ]]; then
    echo "error: required image is unavailable: $image_ref" >&2
    exit 1
  fi
  echo "exists=false" >>"$output_file"
fi
