#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "$repo_root/config/toolchain.env"

# Reuse image toolchains while allowing the host user to install newer versions.
mkdir -p "$ELAN_HOME/toolchains"
for installed in /usr/local/elan/toolchains/*; do
  [[ -d "$installed" ]] || continue
  cached="$ELAN_HOME/toolchains/${installed##*/}"
  if [[ ! -e "$cached" && ! -L "$cached" ]]; then
    ln -s "$installed" "$cached"
  fi
done
elan default "$LEAN_TOOLCHAIN"

exec "$@"
