"""Early safety-guard tests for local release publication."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class PublishReleaseGuardTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copy2(
            ROOT / "scripts/publish-release.sh", scripts / "publish-release.sh"
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def run_publish(
        self, *, path: str | None = None
    ) -> subprocess.CompletedProcess[str]:
        environment = dict(os.environ)
        if path is not None:
            environment["PATH"] = path
        return subprocess.run(
            [str(self.root / "scripts/publish-release.sh"), "alpha"],
            cwd=self.root,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )

    def test_non_main_branch_is_rejected_before_fetch(self) -> None:
        binary = self.root / "bin"
        binary.mkdir()
        git = binary / "git"
        git.write_text(
            """#!/usr/bin/env bash
case "$1 $2" in
  "status --porcelain") exit 0 ;;
  "branch --show-current") echo feature; exit 0 ;;
  fetch*) echo "unexpected fetch" >&2; exit 99 ;;
  *) exit 98 ;;
esac
""",
            encoding="utf-8",
        )
        git.chmod(0o755)

        result = self.run_publish(path=f"{binary}:{os.environ['PATH']}")
        self.assertEqual(result.returncode, 1)
        self.assertIn("main branch", result.stderr)
        self.assertNotIn("unexpected fetch", result.stderr)


if __name__ == "__main__":
    unittest.main()
