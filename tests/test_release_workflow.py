"""Contracts tying publication to reviewed main builds and retained packages."""

import itertools
import unittest
from pathlib import Path

import yaml
from workflow_support import condition_allows

ROOT = Path(__file__).resolve().parent.parent


class ReleaseWorkflowTests(unittest.TestCase):
    def test_release_uses_existing_gates_and_main_only(self):
        build = yaml.safe_load((ROOT / ".github/workflows/build.yml").read_text())
        release = build["jobs"]["release"]
        self.assertIn("check", release["needs"])
        self.assertIn("build-check", release["needs"])
        self.assertIn("plan", release["needs"])
        self.assertEqual(release["uses"], "./.github/workflows/release.yml")
        self.assertNotIn("publish", release["needs"])

    def test_release_condition_accepts_only_reviewed_main_pushes(self):
        workflow = yaml.safe_load((ROOT / ".github/workflows/build.yml").read_text())
        condition = workflow["jobs"]["release"]["if"]
        results = ("success", "failure", "cancelled", "skipped")
        for event, branch, count, source, books in itertools.product(
            ("push", "pull_request", "workflow_dispatch"),
            ("refs/heads/main", "refs/heads/local-work"),
            ("0", "1", "2"),
            results,
            results,
        ):
            with self.subTest(
                event=event, branch=branch, count=count, source=source, books=books
            ):
                context = {
                    "github.event_name": event,
                    "github.ref": branch,
                    "needs.plan.outputs.release_count": count,
                    "needs.check.result": source,
                    "needs.build-check.result": books,
                }
                expected = (
                    event == "push"
                    and branch == "refs/heads/main"
                    and count != "0"
                    and source == books == "success"
                )
                self.assertEqual(condition_allows(condition, context), expected)

    def test_plan_is_independent_of_snapshot_and_unioned_into_builds(self):
        jobs = yaml.safe_load((ROOT / ".github/workflows/build.yml").read_text())[
            "jobs"
        ]
        self.assertNotIn("needs", jobs["plan"])
        planner = next(s for s in jobs["plan"]["steps"] if s.get("id") == "releases")
        self.assertIn("github.event.before", planner["env"]["BASE_SHA"])
        self.assertIn("workflow_dispatch", planner["run"])
        books = next(s for s in jobs["plan"]["steps"] if s.get("id") == "books")
        self.assertIn("RELEASE_MATRIX", books["env"])

    def test_main_runs_preserve_each_version_and_snapshot_writes_are_serial(self):
        workflow = yaml.safe_load((ROOT / ".github/workflows/build.yml").read_text())
        self.assertIn("github.sha", workflow["concurrency"]["group"])
        self.assertIn("pull_request", workflow["concurrency"]["cancel-in-progress"])
        self.assertEqual(
            workflow["jobs"]["publish"]["concurrency"]["group"],
            "development-pdf-snapshot",
        )

    def test_packages_are_preserved_before_publication(self):
        jobs = yaml.safe_load((ROOT / ".github/workflows/build.yml").read_text())[
            "jobs"
        ]
        uploads = [
            s
            for s in jobs["book"]["steps"]
            if s.get("with", {}).get("name") == "${{ matrix.book }}-release"
        ]
        self.assertEqual(len(uploads), 1)
        self.assertEqual(uploads[0]["with"]["retention-days"], 90)
        release = yaml.safe_load((ROOT / ".github/workflows/release.yml").read_text())
        triggers = release.get("on", release.get(True))
        self.assertEqual(set(triggers), {"workflow_call"})
        self.assertIn("github.sha", release["jobs"]["release"]["concurrency"]["group"])


if __name__ == "__main__":
    unittest.main()
