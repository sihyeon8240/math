#!/usr/bin/env bash
set -euo pipefail

if git diff --quiet; then
  exit 0
fi

git fetch --no-tags origin main
if [[ "$(git rev-parse origin/main)" != "$GITHUB_SHA" ]]; then
  echo "A newer main commit exists; leaving image pin updates to its workflow."
  exit 0
fi

branch="automation/image-pin-${GITHUB_RUN_ID:?GITHUB_RUN_ID is required}"
existing_pr="$(gh pr list --state all --head "$branch" --json url --jq '.[0].url // empty')"
if [[ -n "$existing_pr" ]]; then
  echo "Image pin pull request already exists: $existing_pr"
  exit 0
fi

open_pins="$(gh pr list --state open --json headRefName,url --jq \
  '.[] | select(.headRefName | test("^automation/image-pin-[0-9]+$")) | [.headRefName, .url] | @tsv')"
while IFS=$'\t' read -r head_ref url; do
  [[ -n "$head_ref" ]] || continue
  git fetch --no-tags origin "$head_ref"
  if [[ "$(git show FETCH_HEAD:config/container-image.txt)" == "$(cat config/container-image.txt)" ]]; then
    echo "An open pull request already pins this image: $url"
    exit 0
  fi
done <<<"$open_pins"

git config user.name "github-actions[bot]"
git config user.email 41898282+github-actions[bot]@users.noreply.github.com
git add config/container-image.txt .devcontainer/devcontainer.json
git commit -m "build(toolchain): pin tested development image"

# A previous attempt may have pushed the branch before PR creation failed.
if git ls-remote --exit-code --heads origin "$branch" >/dev/null 2>&1; then
  git fetch --no-tags origin "$branch"
  if [[ "$(git rev-parse 'FETCH_HEAD^{tree}')" != "$(git rev-parse 'HEAD^{tree}')" ]]; then
    echo "error: existing image pin branch has different contents: $branch" >&2
    exit 1
  fi
else
  git push origin "HEAD:refs/heads/${branch}"
fi

body="$(mktemp)"
trap 'rm -f -- "$body"' EXIT
cat >"$body" <<'BODY'
Pins the published toolchain image after its native AMD64 and ARM64 smoke tests.

The textbook CI workflow creates this PR only after source, formatting, and PDF
checks pass. Manual image preparation runs the toolchain smoke tests only.

Select **Approve workflows to run** in the PR merge box to start CI for this
GITHUB_TOKEN-created pull request. Review and merge after the required checks pass.
BODY
gh pr create \
  --base main \
  --head "$branch" \
  --title "build(toolchain): pin tested development image" \
  --body-file "$body"
