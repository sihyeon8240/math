#!/usr/bin/env bash

set -Eeuo pipefail

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
        fail "$file not found by kpsewhich"
    fi
}

echo "[Toolchain]"

check_command latexmk
check_command lualatex
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
check_command ruff
check_command elan
check_command lean
check_command lake

if "$PYTHON" -c 'import yaml' >/dev/null 2>&1; then
    pass "PyYAML import succeeded with $PYTHON"
else
    fail "PyYAML is not importable with selected Python: $PYTHON"
fi

tex_dependencies=(
    fontspec.sty microtype.sty graphicx.sty xcolor.sty enumitem.sty
    hyperref.sty cleveref.sty amsmath.sty amssymb.sty amsthm.sty
    mathtools.sty mathrsfs.sty bm.sty romannum.sty aliascnt.sty
    biblatex.sty
)
for dependency in "${tex_dependencies[@]}"; do
    check_tex_file "$dependency"
done

echo
echo "Toolchain dependencies are ready."
