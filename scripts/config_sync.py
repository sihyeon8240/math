#!/usr/bin/env python3
"""Synchronize format-specific consumers from canonical config files."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from repository_config import IMAGE_PATH, ROOT, image_name, load_image, load_toolchain

SHA256 = re.compile(r"[0-9a-f]{64}")


def replace_once(text: str, pattern: str, replacement: str, path: Path) -> str:
    updated, count = re.subn(pattern, replacement, text, flags=re.MULTILINE)
    if count != 1:
        raise ValueError(
            f"{path}: expected exactly one synchronized value, found {count}"
        )
    return updated


def rendered_consumers(root: Path = ROOT) -> dict[Path, str]:
    toolchain = load_toolchain(root / "config/toolchain.env")
    image = load_image(root / "config/container-image.txt")
    devcontainer = root / ".devcontainer/devcontainer.json"
    dev_text = devcontainer.read_text(encoding="utf-8")
    json.loads(dev_text)
    dev_text = replace_once(
        dev_text,
        r'("image"\s*:\s*)"[^"]+"',
        rf'\g<1>"{image}"',
        devcontainer,
    )

    lakefile = root / "lean/lakefile.toml"
    lake_text = replace_once(
        lakefile.read_text(encoding="utf-8"),
        r'^(rev\s*=\s*)"v[^"]+"$',
        rf'\g<1>"v{toolchain["LEAN_VERSION"]}"',
        lakefile,
    )
    pyproject = root / "pyproject.toml"
    pyproject_text = replace_once(
        pyproject.read_text(encoding="utf-8"),
        r'^(target-version\s*=\s*)"py[0-9]+"$',
        rf'\g<1>"py{toolchain["PYTHON_SERIES"].replace(".", "")}"',
        pyproject,
    )
    requirements = (
        f"PyYAML=={toolchain['PYYAML_VERSION']}\nruff=={toolchain['RUFF_VERSION']}\n"
    )
    return {
        devcontainer: dev_text,
        root / "lean/lean-toolchain": toolchain["LEAN_TOOLCHAIN"] + "\n",
        lakefile: lake_text,
        root / ".github/requirements-ci.txt": requirements,
        pyproject: pyproject_text,
    }


def synchronize(*, root: Path = ROOT, check: bool = False) -> list[Path]:
    changed = []
    for path, expected in rendered_consumers(root).items():
        actual = path.read_text(encoding="utf-8")
        if actual == expected:
            continue
        changed.append(path)
        if not check:
            path.write_text(expected, encoding="utf-8")
    return changed


def set_image_digest(digest: str, root: Path = ROOT) -> list[Path]:
    if not SHA256.fullmatch(digest):
        raise ValueError("digest must be exactly 64 lowercase hexadecimal characters")
    image_path = root / IMAGE_PATH.relative_to(ROOT)
    current = load_image(image_path)
    image_path.write_text(f"{image_name(current)}@sha256:{digest}\n", encoding="utf-8")
    return [image_path, *synchronize(root=root)]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true", help="fail on configuration drift"
    )
    parser.add_argument("--set-image-digest", metavar="SHA256")
    args = parser.parse_args()
    try:
        if args.check and args.set_image_digest:
            parser.error("--check and --set-image-digest are mutually exclusive")
        if args.set_image_digest:
            changed = set_image_digest(args.set_image_digest)
        else:
            changed = synchronize(check=args.check)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    if args.check and changed:
        for path in changed:
            print(
                f"error: synchronized configuration is stale: {path}", file=sys.stderr
            )
        return 1
    if changed:
        for path in changed:
            print(f"Updated: {path.relative_to(ROOT)}")
    else:
        print("Repository configuration is synchronized.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
