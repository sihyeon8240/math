#!/usr/bin/env bash

set -Eeuo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${ROOT_DIR}/config/toolchain.env"

PYTHON="${PYTHON:-python3}"

pass() {
  printf "  \033[32m✓\033[0m %s\n" "$1"
}

fail() {
  printf "  \033[31m✗\033[0m %s\n" "$1" >&2
  exit 1
}

check_command() {
  local cmd="$1"

  if command -v "$cmd" >/dev/null 2>&1; then
    pass "$cmd found"
  else
    fail "$cmd not found"
  fi
}

check_tex_file() {
  local file="$1"

  if kpsewhich "$file" >/dev/null 2>&1; then
    pass "$file found"
  else
    fail "$file not found"
  fi
}

check_version() {
  local command="$1"
  local expected="$2"
  local label="$3"
  local actual
  local output
  local rc

  if output="$("$command" --version 2>&1)"; then
    actual="${output%%$'\n'*}"
  else
    rc=$?
    fail "$label version command failed (exit $rc): ${output:-no output}"
  fi
  if [[ "$actual" == *"$expected"* ]]; then
    pass "$label found"
  else
    fail "$label not found: $actual"
  fi
}

echo "[Toolchain]"

check_command latexmk
check_command lualatex
check_command latexindent
check_command biber
check_command make
check_command patch
check_command "$PYTHON"
check_command kpsewhich
check_command rg
check_command gs
check_command tree
check_command git
check_command bash
check_command shellcheck
check_command shfmt
check_command ruff
check_command elan
check_command lean
check_command lake
check_command docker
check_command gh

check_version "$PYTHON" "Python ${PYTHON_VERSION}" "Python ${PYTHON_VERSION}"
check_version latexindent \
  "${LATEXINDENT_VERSION}, ${LATEXINDENT_RELEASE_DATE}" \
  "latexindent ${LATEXINDENT_VERSION}, ${LATEXINDENT_RELEASE_DATE}"
check_version ruff "ruff ${RUFF_VERSION}" "ruff ${RUFF_VERSION}"
check_version shfmt "v${SHFMT_VERSION}" "shfmt ${SHFMT_VERSION}"
check_version elan "elan ${ELAN_VERSION}" "elan ${ELAN_VERSION}"
check_version lean "Lean (version ${LEAN_VERSION}" "Lean ${LEAN_VERSION}"
check_version docker "Docker version ${DOCKER_VERSION}," "Docker ${DOCKER_VERSION}"
check_version gh "gh version ${GH_VERSION}" "GitHub CLI ${GH_VERSION}"

buildx_version="$(docker buildx version 2>&1)"
if [[ "$buildx_version" == *"v${BUILDX_VERSION}"* ]]; then
  pass "Docker Buildx ${BUILDX_VERSION} found"
else
  fail "Docker Buildx ${BUILDX_VERSION} not found: ${buildx_version}"
fi

compose_version="$(docker compose version --short 2>&1)"
if [[ "$compose_version" == "$COMPOSE_VERSION" ]]; then
  pass "Docker Compose ${COMPOSE_VERSION} found"
else
  fail "Docker Compose ${COMPOSE_VERSION} not found: ${compose_version}"
fi

pyyaml_version="$("$PYTHON" -c 'import yaml; print(yaml.__version__)')"
if [[ "$pyyaml_version" == "$PYYAML_VERSION" ]]; then
  pass "PyYAML ${PYYAML_VERSION} found"
else
  fail "PyYAML ${PYYAML_VERSION} not found: $pyyaml_version"
fi

tex_dependencies=(
  fontspec.sty microtype.sty graphicx.sty xcolor.sty enumitem.sty
  hyperref.sty cleveref.sty amsmath.sty amssymb.sty amsthm.sty
  mathtools.sty mathrsfs.sty bm.sty romannum.sty
  biblatex.sty
)
for dependency in "${tex_dependencies[@]}"; do
  check_tex_file "$dependency"
done

echo
echo "Toolchain dependencies are ready."
