#!/usr/bin/env bash
set -Eeuo pipefail

root_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
# shellcheck disable=SC1091
source "${root_dir}/config/toolchain.env"
image="$(<"${root_dir}/config/container-image.txt")"
image_name="${image%@*}"

if [[ -n "${GITHUB_OUTPUT:-}" ]]; then
  {
    echo "image=${image}"
    echo "image_name=${image_name}"
    echo "python=${PYTHON_VERSION}"
    echo "texlive_year=${TEXLIVE_YEAR}"
  } >>"${GITHUB_OUTPUT}"
else
  printf 'IMAGE=%q\n' "${image}"
  printf 'IMAGE_NAME=%q\n' "${image_name}"
  printf 'PYTHON_VERSION=%q\n' "${PYTHON_VERSION}"
  printf 'TEXLIVE_YEAR=%q\n' "${TEXLIVE_YEAR}"
fi

if [[ -n "${GITHUB_ENV:-}" ]]; then
  {
    echo "IMAGE_NAME=${image_name}"
    echo "PYTHON_VERSION=${PYTHON_VERSION}"
    echo "TEXLIVE_YEAR=${TEXLIVE_YEAR}"
  } >>"${GITHUB_ENV}"
fi
