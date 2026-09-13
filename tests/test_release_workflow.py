"""Static contracts for the release workflow."""

from __future__ import annotations

import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class ReleaseWorkflowTests(unittest.TestCase):
    def setUp(self) -> None:
        self.publish = (ROOT / "scripts" / "publish-release.sh").read_text(
            encoding="utf-8"
        )
        self.workflow = (ROOT / ".github/workflows/release.yml").read_text(
            encoding="utf-8"
        )

    def test_publish_does_not_mutate_main_or_overwrite_assets(self) -> None:
        self.assertIn("git tag -a", self.publish)
        self.assertNotIn("git push origin main", self.publish)
        self.assertNotIn("--clobber", self.publish)

    def test_publish_waits_for_validation_and_leaves_release_as_draft(self) -> None:
        self.assertIn("timeout 15m gh run watch", self.publish)
        self.assertNotIn("--draft=false", self.publish)
        self.assertLess(
            self.publish.index("timeout 15m gh run watch"),
            self.publish.index("./scripts/upload-release-assets.sh"),
        )
        self.assertIn("draft: true", self.workflow)

    def test_release_job_requires_validation_and_read_only_contents(self) -> None:
        self.assertIn("contents: read", self.workflow)
        self.assertIn("needs: validate", self.workflow)


if __name__ == "__main__":
    unittest.main()
