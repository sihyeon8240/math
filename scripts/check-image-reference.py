#!/usr/bin/env python3
"""Require local and CI textbook builds to use the same pinned image."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
IMAGE_NAME = "ghcr.io/sihyeon8240/latex"
CI_IMAGE = re.compile(r"(?m)^\s*docker_image:\s*(\S+)\s*$")
TEST_IMAGE = re.compile(r'(?m)^(EXPECTED_IMAGE\s*=\s*)"[^"]+"[ \t]*$')
SHA256_DIGEST = re.compile(r"[0-9a-f]{64}")


def check(devcontainer: Path, workflows: list[Path]) -> str:
    try:
        local = json.loads(devcontainer.read_text(encoding="utf-8"))["image"]
    except (OSError, UnicodeError, json.JSONDecodeError, KeyError) as error:
        raise ValueError(f"cannot read devcontainer image: {error}") from error
    for workflow in workflows:
        matches = CI_IMAGE.findall(workflow.read_text(encoding="utf-8"))
        if len(matches) != 1:
            raise ValueError(
                f"{workflow} must contain exactly one docker_image reference"
            )
        if local != matches[0]:
            raise ValueError(
                "textbook build image mismatch: "
                f"devcontainer uses {local!r}, {workflow} uses {matches[0]!r}"
            )
    if not re.fullmatch(rf"{re.escape(IMAGE_NAME)}@sha256:[0-9a-f]{{64}}", local):
        raise ValueError(f"textbook build image is not pinned immutably: {local!r}")
    return local


def update(devcontainer: Path, workflows: list[Path], test: Path, digest: str) -> None:
    if not SHA256_DIGEST.fullmatch(digest):
        raise ValueError("digest must be exactly 64 lowercase hexadecimal characters")
    image = f"{IMAGE_NAME}@sha256:{digest}"
    dev_text = devcontainer.read_text(encoding="utf-8")
    json.loads(dev_text)
    updated_dev, dev_count = re.subn(
        r"(\"image\"\s*:\s*)\"[^\"]+\"",
        lambda match: f'{match.group(1)}"{image}"',
        dev_text,
    )
    updated_workflows = []
    for workflow in workflows:
        workflow_text = workflow.read_text(encoding="utf-8")
        updated_workflow, workflow_count = CI_IMAGE.subn(
            lambda match: match.group(0).replace(match.group(1), image),
            workflow_text,
        )
        if workflow_count != 1:
            raise ValueError(
                f"{workflow} must contain exactly one docker_image reference"
            )
        updated_workflows.append((workflow, updated_workflow))
    test_text = test.read_text(encoding="utf-8")
    updated_test, test_count = TEST_IMAGE.subn(
        lambda match: f'{match.group(1)}"{image}"',
        test_text,
    )
    if dev_count != 1:
        raise ValueError(f"{devcontainer} must contain exactly one image reference")
    if test_count != 1:
        raise ValueError(f"{test} must contain exactly one EXPECTED_IMAGE reference")
    devcontainer.write_text(updated_dev, encoding="utf-8")
    for workflow, updated_workflow in updated_workflows:
        workflow.write_text(updated_workflow, encoding="utf-8")
    test.write_text(updated_test, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--devcontainer", type=Path, default=ROOT / ".devcontainer/devcontainer.json"
    )
    parser.add_argument(
        "--workflow",
        type=Path,
        action="append",
        default=None,
        help="workflow to check and update (may be repeated)",
    )
    parser.add_argument(
        "--test", type=Path, default=ROOT / "tests/test_image_reference.py"
    )
    parser.add_argument(
        "--set-digest", metavar="SHA256", help="update all pinned references"
    )
    args = parser.parse_args()
    workflows = args.workflow or [
        ROOT / ".github/workflows/build.yml",
        ROOT / ".github/workflows/check.yml",
    ]
    try:
        if args.set_digest:
            update(args.devcontainer, workflows, args.test, args.set_digest)
        image = check(args.devcontainer, workflows)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(f"Textbook build image references match: {image}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
