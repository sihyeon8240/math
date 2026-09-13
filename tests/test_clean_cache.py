"""Tests for selective local-cache cleanup."""

from __future__ import annotations

import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class CleanCacheTests(unittest.TestCase):
    def run_clean(self, root: Path, scope: str) -> subprocess.CompletedProcess[str]:
        scripts = root / "scripts"
        scripts.mkdir(exist_ok=True)
        shutil.copy2(ROOT / "scripts/clean-cache.sh", scripts / "clean-cache.sh")
        return subprocess.run(
            [str(scripts / "clean-cache.sh"), scope],
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )

    def populate_caches(self, root: Path) -> dict[str, Path]:
        caches = {
            "lake": root / "lean/.lake/cache",
            "tex": root / ".latexindent_cache/cache",
            "ruff": root / ".ruff_cache/cache",
            "py": root / "package/__pycache__/module.pyc",
        }
        for path in caches.values():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("cache", encoding="utf-8")
        return caches

    def test_each_scope_removes_only_selected_cache(self) -> None:
        for scope in ("lake", "tex", "ruff", "py"):
            with self.subTest(scope=scope), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                caches = self.populate_caches(root)
                result = self.run_clean(root, scope)

                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertFalse(caches[scope].exists())
                self.assertTrue(
                    all(path.exists() for name, path in caches.items() if name != scope)
                )

    def test_all_removes_every_cache(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            caches = self.populate_caches(root)
            result = self.run_clean(root, "all")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(all(not path.exists() for path in caches.values()))

    def test_rejects_unknown_scope(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_clean(Path(directory), "unknown")

            self.assertEqual(result.returncode, 2)
            self.assertIn("usage:", result.stderr)


if __name__ == "__main__":
    unittest.main()
