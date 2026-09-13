#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 <book-slug> <package-directory>" >&2
  exit 2
fi
if [[ "${GITHUB_ACTIONS:-}" != true || "${GITHUB_EVENT_NAME:-}" != push ||
  "${GITHUB_REF:-}" != refs/heads/main ]]; then
  echo "error: publication requires a main push workflow" >&2
  exit 1
fi
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
slug="$1"
package="$(cd "$2" && pwd)"
version="$(python3 scripts/books.py version "$slug")"
tag="$slug-v$version"
./scripts/release-plan.sh "$tag" >/dev/null
[[ "$(git rev-parse HEAD)" == "$GITHUB_SHA" ]] || {
  echo "error: checkout does not match the validated commit" >&2
  exit 1
}
git fetch --no-tags origin main
git merge-base --is-ancestor "$GITHUB_SHA" origin/main
(
  cd "$package"
  test -s "$tag.pdf"
  test "$(wc -l <SHA256SUMS)" -eq 1
  [[ "$(cat SHA256SUMS)" == "$(sha256sum "$tag.pdf")" ]]
)
# Fetch tags without force: an existing tag must never move.
git fetch origin 'refs/tags/*:refs/tags/*'
if git rev-parse --verify --quiet "refs/tags/$tag" >/dev/null; then
  [[ "$(git rev-list -n 1 "$tag")" == "$GITHUB_SHA" &&
  "$(git cat-file -t "refs/tags/$tag")" == tag ]] || {
    echo "error: existing release tag has a conflicting commit or is not annotated" >&2
    exit 1
  }
else
  git config user.name 'github-actions[bot]'
  git config user.email '41898282+github-actions[bot]@users.noreply.github.com'
  git tag -a "$tag" "$GITHUB_SHA" -m "Release $slug version $version"
  git push origin "refs/tags/$tag"
fi
# Listing must succeed; authorization/network failures are not missing releases.
draft="$(gh api "repos/$GITHUB_REPOSITORY/releases" --paginate \
  --jq ".[] | select(.tag_name == \"$tag\") | .draft")"
if [[ "$draft" == false ]]; then
  echo "==> $tag is already public; leaving it unchanged"
  exit 0
fi
if [[ -z "$draft" ]]; then
  options=(--draft --verify-tag --generate-notes --latest=false --title "$tag")
  [[ "$version" != *-* ]] || options+=(--prerelease)
  gh release create "$tag" "${options[@]}"
fi
./scripts/upload-release-assets.sh "$tag" "$package/$tag.pdf" "$package/SHA256SUMS"
# Verify bytes downloaded from GitHub before making the release public.
verification="$(mktemp -d)"
trap 'rm -rf -- "$verification"' EXIT
gh release download "$tag" --pattern "$tag.pdf" --pattern SHA256SUMS --dir "$verification"
cmp "$package/$tag.pdf" "$verification/$tag.pdf"
cmp "$package/SHA256SUMS" "$verification/SHA256SUMS"
gh release edit "$tag" --draft=false --latest=false
echo "==> Published $tag"
