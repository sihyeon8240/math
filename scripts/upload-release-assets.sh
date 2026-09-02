#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 3 ]]; then
  echo "usage: $0 <tag> <pdf> <checksums>" >&2
  exit 2
fi

tag="$1"
pdf="$2"
checksums="$3"
temporary="$(mktemp -d)"
trap 'rm -rf -- "$temporary"' EXIT

existing_assets="$(gh release view "$tag" --json assets --jq '.assets[].name')"
uploads=()
for local_asset in "$pdf" "$checksums"; do
  name="${local_asset##*/}"
  if grep -Fxq "$name" <<<"$existing_assets"; then
    gh release download "$tag" --pattern "$name" --dir "$temporary"
    if ! cmp -s "$local_asset" "$temporary/$name"; then
      echo "error: release asset already exists with different content: $name" >&2
      exit 1
    fi
    echo "==> Existing release asset matches: $name"
  else
    uploads+=("$local_asset")
  fi
done

if ((${#uploads[@]} > 0)); then
  gh release upload "$tag" "${uploads[@]}"
fi
