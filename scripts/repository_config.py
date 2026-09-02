"""Load and validate repository-wide toolchain configuration."""

from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLCHAIN_PATH = ROOT / "config/toolchain.env"
IMAGE_PATH = ROOT / "config/container-image.txt"

ASSIGNMENT = re.compile(r"([A-Z][A-Z0-9_]*)=([A-Za-z0-9._:/+-]+)")
IMAGE = re.compile(r"ghcr\.io/[a-z0-9-]+/[a-z0-9-]+@sha256:[0-9a-f]{64}")
SHA256 = re.compile(r"[0-9a-f]{64}")
REQUIRED_TOOLCHAIN_KEYS = {
    "TEXLIVE_YEAR",
    "TEXLIVE_ARCHIVE_DATE",
    "TEXLIVE_INSTALLER_SHA256",
    "PYTHON_VERSION",
    "PYTHON_SERIES",
    "PYTHON_SHA256",
    "ELAN_VERSION",
    "ELAN_SHA256_AMD64",
    "ELAN_SHA256_ARM64",
    "RUFF_VERSION",
    "RUFF_SHA256_AMD64",
    "RUFF_SHA256_ARM64",
    "SHFMT_VERSION",
    "SHFMT_SHA256_AMD64",
    "SHFMT_SHA256_ARM64",
    "LATEXINDENT_VERSION",
    "LATEXINDENT_RELEASE_DATE",
    "LATEXINDENT_SHA256_AMD64",
    "LATEXINDENT_SHA256_ARM64",
    "PYYAML_VERSION",
    "LEAN_VERSION",
    "LEAN_TOOLCHAIN",
    "DOCKER_VERSION",
    "DOCKER_SHA256_AMD64",
    "DOCKER_SHA256_ARM64",
    "BUILDX_VERSION",
    "BUILDX_SHA256_AMD64",
    "BUILDX_SHA256_ARM64",
    "COMPOSE_VERSION",
    "COMPOSE_SHA256_AMD64",
    "COMPOSE_SHA256_ARM64",
    "GH_VERSION",
    "GH_SHA256_AMD64",
    "GH_SHA256_ARM64",
}


def load_toolchain(path: Path = TOOLCHAIN_PATH) -> dict[str, str]:
    values: dict[str, str] = {}
    for number, raw_line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        match = ASSIGNMENT.fullmatch(line)
        if not match:
            raise ValueError(f"{path}:{number}: invalid configuration assignment")
        key, value = match.groups()
        if key in values:
            raise ValueError(f"{path}:{number}: duplicate key {key}")
        values[key] = value
    missing = sorted(REQUIRED_TOOLCHAIN_KEYS - values.keys())
    extra = sorted(values.keys() - REQUIRED_TOOLCHAIN_KEYS)
    if missing:
        raise ValueError(f"{path}: missing keys: {', '.join(missing)}")
    if extra:
        raise ValueError(f"{path}: unknown keys: {', '.join(extra)}")
    for key in (key for key in values if "SHA256" in key):
        if not SHA256.fullmatch(values[key]):
            raise ValueError(f"{path}: {key} must be a lowercase SHA-256 digest")
    if not values["PYTHON_VERSION"].startswith(values["PYTHON_SERIES"] + "."):
        raise ValueError(f"{path}: PYTHON_VERSION must match PYTHON_SERIES")
    expected_lean = f"leanprover/lean4:v{values['LEAN_VERSION']}"
    if values["LEAN_TOOLCHAIN"] != expected_lean:
        raise ValueError(f"{path}: LEAN_TOOLCHAIN must be {expected_lean}")
    return values


def load_image(path: Path = IMAGE_PATH) -> str:
    image = path.read_text(encoding="utf-8").strip()
    if not IMAGE.fullmatch(image):
        raise ValueError(f"{path}: expected an immutable GHCR image reference")
    return image


def image_name(image: str) -> str:
    return image.split("@", 1)[0]
