"""Tests for selective local-cache cleanup."""

from __future__ import annotations

import os
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
            "tex": root / ".cache/latexindent/cache",
            "ruff": root / ".cache/ruff/cache",
            "py": root / ".cache/python/module.pyc",
            "mathlib": root / ".cache/mathlib/cache",
        }
        for path in caches.values():
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("cache", encoding="utf-8")
        return caches

    def test_each_scope_removes_only_selected_cache(self) -> None:
        for scope in ("lake", "mathlib", "tex", "ruff", "py"):
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

    def test_cleanup_preserves_unknown_caches_and_unrelated_bytecode(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.populate_caches(root)
            preserved = (root / ".cache/custom/keep.pyc", root / "package/keep.pyc")
            for path in preserved:
                path.parent.mkdir(parents=True)
                path.write_text("keep")

            result = self.run_clean(root, "all")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(all(path.read_text() == "keep" for path in preserved))

    def test_rejects_symlinked_cache_directories_and_parents(self) -> None:
        for relative, scope in ((".cache/ruff", "ruff"), ("lean/.lake", "lake")):
            for parent_link in (False, True):
                with (
                    self.subTest(relative=relative, parent_link=parent_link),
                    tempfile.TemporaryDirectory() as directory,
                ):
                    root = Path(directory) / "repo"
                    root.mkdir()
                    external = Path(directory) / "external"
                    external.mkdir()
                    cache = root / relative
                    if parent_link:
                        cache.parent.symlink_to(external, target_is_directory=True)
                        external_cache = external / cache.name
                        external_cache.mkdir()
                    else:
                        cache.parent.mkdir()
                        cache.symlink_to(external, target_is_directory=True)
                        external_cache = external
                    sentinel = external_cache / "keep"
                    sentinel.write_text("keep")

                    result = self.run_clean(root, scope)

                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("refusing symlinked cache path", result.stderr)
                    self.assertEqual(sentinel.read_text(), "keep")
                    self.assertTrue(cache.exists())

    def test_cleanup_does_not_follow_links_inside_cache(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "repo"
            cache = root / ".cache/ruff"
            cache.mkdir(parents=True)
            external = Path(directory) / "external"
            external.mkdir()
            sentinel = external / "keep"
            sentinel.write_text("keep")
            (cache / "link").symlink_to(external, target_is_directory=True)

            result = self.run_clean(root, "ruff")

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(cache.exists())
            self.assertEqual(sentinel.read_text(), "keep")

    def test_make_exports_absolute_defaults_and_respects_overrides(self) -> None:
        with tempfile.TemporaryDirectory(prefix="cache paths ") as directory:
            root = Path(directory)
            environment = dict(os.environ)
            variables = ("PYTHONPYCACHEPREFIX", "MATHLIB_CACHE_DIR")
            for variable in variables:
                environment.pop(variable, None)

            for override in (False, True):
                with self.subTest(override=override):
                    expected = [
                        str(root / ".cache" / name) for name in ("python", "mathlib")
                    ]
                    if override:
                        expected = [str(root / "custom" / name) for name in variables]
                        environment.update(zip(variables, expected))
                    result = subprocess.run(
                        [
                            "make",
                            "--no-print-directory",
                            "-f",
                            str(ROOT / "Makefile"),
                            "--eval=cache-environment:\n\t@printenv PYTHONPYCACHEPREFIX MATHLIB_CACHE_DIR",
                            "cache-environment",
                        ],
                        cwd=root,
                        env=environment,
                        capture_output=True,
                        text=True,
                        check=False,
                    )
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stdout.splitlines(), expected)

    def test_rejects_unknown_scope(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            result = self.run_clean(Path(directory), "unknown")

            self.assertEqual(result.returncode, 2)
            self.assertIn("usage:", result.stderr)


if __name__ == "__main__":
    unittest.main()
