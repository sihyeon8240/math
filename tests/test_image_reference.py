"""Checks for canonical repository configuration and synchronized consumers."""

from __future__ import annotations

import importlib.util
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))

CONFIG_SPEC = importlib.util.spec_from_file_location(
    "repository_config", ROOT / "scripts/repository_config.py"
)
assert CONFIG_SPEC and CONFIG_SPEC.loader
CONFIG = importlib.util.module_from_spec(CONFIG_SPEC)
CONFIG_SPEC.loader.exec_module(CONFIG)

SYNC_SPEC = importlib.util.spec_from_file_location(
    "config_sync", ROOT / "scripts/config_sync.py"
)
assert SYNC_SPEC and SYNC_SPEC.loader
SYNC = importlib.util.module_from_spec(SYNC_SPEC)
SYNC_SPEC.loader.exec_module(SYNC)


class ConfigurationTests(unittest.TestCase):
    def make_repository(self, root: Path) -> None:
        for relative in (
            "config",
            ".devcontainer",
            ".github",
            "lean",
        ):
            (root / relative).mkdir(parents=True, exist_ok=True)
        shutil.copy(ROOT / "config/toolchain.env", root / "config/toolchain.env")
        shutil.copy(
            ROOT / "config/container-image.txt", root / "config/container-image.txt"
        )
        shutil.copy(
            ROOT / ".devcontainer/devcontainer.json",
            root / ".devcontainer/devcontainer.json",
        )
        shutil.copy(
            ROOT / ".github/requirements-ci.txt",
            root / ".github/requirements-ci.txt",
        )
        shutil.copy(ROOT / "lean/lean-toolchain", root / "lean/lean-toolchain")
        shutil.copy(ROOT / "lean/lakefile.toml", root / "lean/lakefile.toml")
        shutil.copy(ROOT / "pyproject.toml", root / "pyproject.toml")

    def test_repository_configuration_is_synchronized(self) -> None:
        self.assertEqual(SYNC.synchronize(check=True), [])
        image = CONFIG.load_image()
        devcontainer = json.loads(
            (ROOT / ".devcontainer/devcontainer.json").read_text(encoding="utf-8")
        )
        self.assertEqual(devcontainer["image"], image)
        build = (ROOT / ".github/workflows/build.yml").read_text(encoding="utf-8")
        check = (ROOT / ".github/workflows/check.yml").read_text(encoding="utf-8")
        self.assertIn("needs.prepare-image.outputs.image", build)
        self.assertIn("needs.prepare-image.outputs.image", check)
        self.assertNotIn(image, build)
        self.assertNotIn(image, check)

    def test_invalid_mutable_image_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "image.txt"
            path.write_text("ghcr.io/example/latex:latest\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "immutable GHCR"):
                CONFIG.load_image(path)

    def test_toolchain_relationships_are_validated(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "toolchain.env"
            text = (ROOT / "config/toolchain.env").read_text(encoding="utf-8")
            path.write_text(
                text.replace(
                    "LEAN_TOOLCHAIN=leanprover/lean4:v4.33.1",
                    "LEAN_TOOLCHAIN=leanprover/lean4:v4.32.0",
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "LEAN_TOOLCHAIN must be"):
                CONFIG.load_toolchain(path)

    def test_drift_is_reported_and_synchronized(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.make_repository(root)
            (root / "lean/lean-toolchain").write_text(
                "leanprover/lean4:v0.0.0\n", encoding="utf-8"
            )
            self.assertEqual(
                SYNC.synchronize(root=root, check=True),
                [root / "lean/lean-toolchain"],
            )
            self.assertEqual(
                SYNC.synchronize(root=root),
                [root / "lean/lean-toolchain"],
            )
            self.assertEqual(SYNC.synchronize(root=root, check=True), [])

    def test_image_update_changes_only_canonical_and_derived_files(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.make_repository(root)
            changed = SYNC.set_image_digest("b" * 64, root=root)
            expected = f"ghcr.io/sihyeon8240/latex@sha256:{'b' * 64}"
            self.assertEqual(
                (root / "config/container-image.txt").read_text(encoding="utf-8"),
                expected + "\n",
            )
            devcontainer = json.loads(
                (root / ".devcontainer/devcontainer.json").read_text(encoding="utf-8")
            )
            self.assertEqual(devcontainer["image"], expected)
            self.assertEqual(
                changed,
                [
                    root / "config/container-image.txt",
                    root / ".devcontainer/devcontainer.json",
                ],
            )

    def test_image_update_rejects_non_sha256_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.make_repository(root)
            with self.assertRaisesRegex(ValueError, "exactly 64 lowercase"):
                SYNC.set_image_digest("a" * 40, root=root)


if __name__ == "__main__":
    unittest.main()
