"""Behavior tests for release tag planning."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class ReleasePlanTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copy2(ROOT / "scripts/release-plan.sh", scripts / "release-plan.sh")
        (scripts / "books.py").write_text(
            textwrap.dedent("""\
            import os
            import sys

            command = sys.argv[1]
            if command == "list":
                print(os.environ.get("RELEASABLE", "alpha"))
            elif command == "version":
                print(os.environ.get("VERSION", "1.2.3"))
            else:
                raise SystemExit(2)
            """),
            encoding="utf-8",
        )

    def run_plan(
        self, tag: str, **environment: str
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(self.root / "scripts/release-plan.sh"), tag],
            cwd=self.root,
            env={**os.environ, "PYTHON": sys.executable, **environment},
            capture_output=True,
            text=True,
            check=False,
            timeout=10,
        )

    def test_valid_tag_exports_version_and_single_book_matrix(self) -> None:
        result = self.run_plan("alpha-v1.2.3")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            result.stdout.splitlines(),
            ["alpha_version=1.2.3", "version=1.2.3", 'matrix={"book":["alpha"]}'],
        )

    def test_hyphenated_prerelease_tags_are_accepted(self) -> None:
        for version in ("1.2.3--alpha", "1.2.3-alpha--beta", "1.2.3-rc.1"):
            with self.subTest(version=version):
                result = self.run_plan(f"alpha-v{version}", VERSION=version)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(f"version={version}\n", result.stdout)

    def test_invalid_or_disabled_book_tag_is_rejected(self) -> None:
        invalid = self.run_plan("alpha-1.2.3")
        disabled = self.run_plan("beta-v1.2.3")
        self.assertEqual(invalid.returncode, 2)
        self.assertIn("invalid release tag", invalid.stderr)
        self.assertEqual(disabled.returncode, 2)
        self.assertIn("not enabled for release", disabled.stderr)

    def test_manifest_version_must_match_tag(self) -> None:
        result = self.run_plan("alpha-v1.2.4", VERSION="1.2.3")
        self.assertEqual(result.returncode, 1)
        self.assertIn("tag version 1.2.4 does not match", result.stderr)


if __name__ == "__main__":
    unittest.main()
