"""Static contracts for the release workflow."""

from __future__ import annotations

import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class ReleaseWorkflowTests(unittest.TestCase):
    def test_release_workflow_invariants(self) -> None:
        publish = (ROOT / "scripts" / "publish-release.sh").read_text(encoding="utf-8")
        plan = (ROOT / "scripts" / "release-plan.sh").read_text(encoding="utf-8")
        check_script = (ROOT / "scripts" / "check.sh").read_text(encoding="utf-8")
        repository_check = (ROOT / "scripts" / "check-repository.sh").read_text(
            encoding="utf-8"
        )
        makefile = (ROOT / "Makefile").read_text(encoding="utf-8")
        workflow = (ROOT / ".github/workflows/release.yml").read_text(encoding="utf-8")

        self.assertIn('[[ "$head_commit" != "$remote_main_commit" ]]', publish)
        self.assertIn("git tag -a", publish)
        self.assertNotIn("git push origin main", publish)
        self.assertNotIn("--clobber", publish)
        self.assertIn("timeout 15m gh run watch", publish)
        self.assertNotIn("all-books-v", plan)
        self.assertNotRegex(makefile, r"(?m)^dist:")
        self.assertRegex(makefile, r"(?m)^check:$")
        self.assertIn("STRICT_REQUESTED :=", makefile)
        self.assertIn("CHECK_LOG_STRICT=1 ./scripts/check.sh", makefile)
        self.assertIn('format-tex.sh" --check', check_script)
        self.assertIn('format-python.sh" --check', check_script)
        self.assertNotIn("format-python.sh --check", repository_check)
        self.assertNotRegex(makefile, r"(?m)^check-strict:$")
        self.assertIn("contents: read", workflow)
        self.assertIn("needs: validate", workflow)
        self.assertIn("draft: true", workflow)
        self.assertIn('gh release edit "$tag" --draft=false', publish)


if __name__ == "__main__":
    unittest.main()
