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

    def test_success_uploads_to_a_draft_without_publishing(self) -> None:
        binary = self.root / "bin"
        binary.mkdir()
        scripts = self.root / "scripts"
        executables = {
            binary / "git": """#!/usr/bin/env bash
case "$1 $2" in
  "status --porcelain"|"fetch --no-tags"|"tag -a"|"push origin") exit 0 ;;
  "branch --show-current") echo main ;;
  "rev-parse HEAD"|"rev-parse origin/main") echo commit ;;
  "rev-parse --verify") exit 1 ;;
  *) echo "unexpected git call: $*" >&2; exit 98 ;;
esac
""",
            binary / "gh": """#!/usr/bin/env bash
echo "$*" >> gh-calls
case "$1 $2" in
  "run list") echo 7 ;;
  "run watch") exit 0 ;;
  "release view") cat draft-state ;;
  *) echo "unexpected gh call: $*" >&2; exit 98 ;;
esac
""",
            scripts / "build-book.sh": "#!/usr/bin/env bash\nexit 0\n",
            scripts / "release-plan.sh": "#!/usr/bin/env bash\nexit 0\n",
            scripts
            / "package-book.sh": '#!/usr/bin/env bash\necho pdf > "$2/alpha-v1.2.3.pdf"\n',
            scripts
            / "upload-release-assets.sh": '#!/usr/bin/env bash\ntest -f "$2" && test -f "$3" && touch uploaded\n',
        }
        for path, content in executables.items():
            path.write_text(content)
            path.chmod(0o755)
        (scripts / "books.py").write_text(
            'import sys\nif sys.argv[1] == "version": print("1.2.3")\n'
        )
        (self.root / "draft-state").write_text("true\n")
        result = self.run_publish(path=f"{binary}:{os.environ['PATH']}")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((self.root / "uploaded").exists())
        self.assertIn("remains a draft", result.stdout)
        self.assertNotIn("release edit", (self.root / "gh-calls").read_text())
        (self.root / "uploaded").unlink()
        (self.root / "draft-state").write_text("false\n")
        result = self.run_publish(path=f"{binary}:{os.environ['PATH']}")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("already public", result.stderr)
        self.assertFalse((self.root / "uploaded").exists())

    def test_dirty_worktree_is_rejected_before_branch_lookup(self) -> None:
        binary = self.root / "bin"
        binary.mkdir()
        git = binary / "git"
        git.write_text(
            """#!/usr/bin/env bash
case "$1 $2" in
  "status --porcelain") echo " M README.md"; exit 0 ;;
  "status --short") echo " M README.md"; exit 0 ;;
  "branch --show-current") echo "unexpected branch lookup" >&2; exit 99 ;;
  *) exit 98 ;;
esac
""",
            encoding="utf-8",
        )
        git.chmod(0o755)

        result = self.run_publish(path=f"{binary}:{os.environ['PATH']}")
        self.assertEqual(result.returncode, 1)
        self.assertIn("repository must be clean", result.stderr)
        self.assertIn("M README.md", result.stderr)
        self.assertNotIn("unexpected branch lookup", result.stderr)

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

    def test_remote_main_mismatch_is_rejected_before_manifest_validation(self) -> None:
        binary = self.root / "bin"
        binary.mkdir()
        git = binary / "git"
        git.write_text(
            """#!/usr/bin/env bash
case "$1 $2" in
  "status --porcelain") exit 0 ;;
  "branch --show-current") echo main; exit 0 ;;
  "fetch --no-tags") exit 0 ;;
  "rev-parse HEAD") echo local-commit; exit 0 ;;
  "rev-parse origin/main") echo remote-commit; exit 0 ;;
  *) echo "unexpected git call: $*" >&2; exit 98 ;;
esac
""",
            encoding="utf-8",
        )
        git.chmod(0o755)

        result = self.run_publish(path=f"{binary}:{os.environ['PATH']}")
        self.assertEqual(result.returncode, 1)
        self.assertIn("HEAD must exactly match origin/main", result.stderr)
        self.assertIn("local-commit", result.stderr)
        self.assertIn("remote-commit", result.stderr)


if __name__ == "__main__":
    unittest.main()
