"""Checks for the shared textbook build image reference."""

from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXPECTED_IMAGE = "ghcr.io/sihyeon8240/latex@sha256:2f91bda5f4330df41e006c455a356b485b68f923f002ca5b12861b76dc1f0a0f"
SPEC = importlib.util.spec_from_file_location(
    "check_image_reference", ROOT / "scripts/check-image-reference.py"
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ImageReferenceTests(unittest.TestCase):
    def write_inputs(self, root: Path, local: str, ci: str) -> tuple[Path, Path]:
        devcontainer = root / "devcontainer.json"
        workflow = root / "build.yml"
        devcontainer.write_text(json.dumps({"image": local}), encoding="utf-8")
        workflow.write_text(f"docker_image: {ci}\n", encoding="utf-8")
        return devcontainer, workflow

    def test_repository_references_match(self) -> None:
        self.assertEqual(
            MODULE.check(
                ROOT / ".devcontainer/devcontainer.json",
                [
                    ROOT / ".github/workflows/build.yml",
                    ROOT / ".github/workflows/check.yml",
                ],
            ),
            EXPECTED_IMAGE,
        )

    def test_mismatch_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paths = self.write_inputs(
                Path(temporary),
                f"{MODULE.IMAGE_NAME}@sha256:{'a' * 64}",
                f"{MODULE.IMAGE_NAME}@sha256:{'b' * 64}",
            )
            with self.assertRaisesRegex(ValueError, "image mismatch"):
                MODULE.check(paths[0], [paths[1]])

    def test_mutable_tag_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paths = self.write_inputs(
                Path(temporary),
                f"{MODULE.IMAGE_NAME}:latest",
                f"{MODULE.IMAGE_NAME}:latest",
            )
            with self.assertRaisesRegex(ValueError, "not pinned immutably"):
                MODULE.check(paths[0], [paths[1]])

    def test_update_changes_all_references(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paths = self.write_inputs(
                root,
                f"{MODULE.IMAGE_NAME}@sha256:{'a' * 64}",
                f"{MODULE.IMAGE_NAME}@sha256:{'a' * 64}",
            )
            check_workflow = root / "check.yml"
            check_workflow.write_text(
                paths[1].read_text(encoding="utf-8"), encoding="utf-8"
            )
            workflows = [paths[1], check_workflow]
            test = root / "test_image_reference.py"
            test.write_text(
                f'EXPECTED_IMAGE = "{MODULE.IMAGE_NAME}@sha256:{"a" * 64}"\n',
                encoding="utf-8",
            )
            MODULE.update(paths[0], workflows, test, "b" * 64)
            expected = f"{MODULE.IMAGE_NAME}@sha256:{'b' * 64}"
            self.assertEqual(MODULE.check(paths[0], workflows), expected)
            self.assertEqual(
                test.read_text(encoding="utf-8"),
                f'EXPECTED_IMAGE = "{expected}"\n',
            )

    def test_update_rejects_non_sha256_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paths = self.write_inputs(
                root,
                f"{MODULE.IMAGE_NAME}@sha256:{'a' * 64}",
                f"{MODULE.IMAGE_NAME}@sha256:{'a' * 64}",
            )
            test = root / "test_image_reference.py"
            test.write_text(f'EXPECTED_IMAGE = "{EXPECTED_IMAGE}"\n', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "exactly 64 lowercase"):
                MODULE.update(paths[0], [paths[1]], test, "a" * 40)


if __name__ == "__main__":
    unittest.main()
