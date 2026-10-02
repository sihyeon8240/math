"""PDF snapshot updates, publication gates, and Pages sources."""

from __future__ import annotations

import itertools
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml
from test_support import write_executable
from workflow_support import build_workflow, condition_allows

ROOT = Path(__file__).resolve().parent.parent


class SnapshotWorkflowTests(unittest.TestCase):
    def run_pdf_update(
        self,
        updated: dict[str, bytes],
        existing: dict[str, bytes],
        *,
        registered=("alpha", "beta"),
        site=("alpha", "beta"),
    ):
        workflow = build_workflow()
        publish = next(
            step["run"]
            for step in workflow["jobs"]["publish"]["steps"]
            if step.get("id") == "publish"
        )
        start = publish.index("mkdir -p snapshot/pdf")
        end = publish.index("printf '%s\\n' \"$GITHUB_SHA\"")
        script = "set -euo pipefail\n" + publish[start:end]

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "snapshot" / "pdf").mkdir(parents=True)
            for name, data in existing.items():
                (root / "snapshot" / "pdf" / name).write_bytes(data)
            if updated:
                (root / "updated-pdfs").mkdir()
                for name, data in updated.items():
                    (root / "updated-pdfs" / name).write_bytes(data)
            (root / "scripts").mkdir()
            (root / "scripts" / "books.py").write_text(
                """#!/usr/bin/env python3
import json
import os
import sys
registered = os.environ["REGISTERED"].split()
site = os.environ["SITE"].split()
if sys.argv[1] == "require":
    with open(os.environ["REQUIRE_LOG"], "a", encoding="utf-8") as log:
        log.write(sys.argv[2] + "\\n")
    raise SystemExit(0 if sys.argv[2] in registered else 1)
if sys.argv[1:] == ["list", "--for", "site"]:
    print(*site, sep="\\n")
    raise SystemExit(0)
raise SystemExit(2)
""",
                encoding="utf-8",
            )
            require_log = root / "require.log"
            result = subprocess.run(
                ["bash", "-c", script],
                cwd=root,
                text=True,
                capture_output=True,
                check=False,
                env={
                    **os.environ,
                    "REGISTERED": " ".join(registered),
                    "SITE": " ".join(site),
                    "REQUIRE_LOG": str(require_log),
                },
                timeout=30,
            )
            snapshot = {
                path.name: path.read_bytes()
                for path in (root / "snapshot" / "pdf").iterdir()
            }
            required = (
                require_log.read_text(encoding="utf-8").splitlines()
                if require_log.exists()
                else []
            )
            return result, snapshot, required

    def run_snapshot(self, **values: str):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            output = root / "output"
            git = root / "git"
            write_executable(
                git,
                """#!/usr/bin/env bash
case "$1" in
  fetch) exit "${FETCH_STATUS:-0}" ;;
  show) printf '%s' "${SOURCE_SHA:-}"; exit "${SHOW_STATUS:-0}" ;;
  cat-file) exit "${COMMIT_STATUS:-0}" ;;
  merge-base) exit "${ANCESTOR_STATUS:-0}" ;;
  *) exit 2 ;;
esac
""",
            )
            env = {
                **os.environ,
                **values,
                "GITHUB_OUTPUT": str(output),
                "PATH": f"{root}:{os.environ['PATH']}",
            }
            result = subprocess.run(
                [ROOT / "scripts/snapshot-base.sh"],
                env=env,
                text=True,
                capture_output=True,
                check=False,
                timeout=30,
            )
            return result, output.read_text(encoding="utf-8")

    def test_snapshot_base_valid_sha(self):
        sha = "a" * 40
        result, output = self.run_snapshot(SOURCE_SHA=sha)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, f"base={sha}\n")

    def test_snapshot_base_failures_emit_explicit_empty_base(self):
        cases = (
            {"FETCH_STATUS": "1"},
            {"SHOW_STATUS": "1"},
            {"SOURCE_SHA": "invalid"},
            {"SOURCE_SHA": "a" * 40, "COMMIT_STATUS": "1"},
            {"SOURCE_SHA": "a" * 40, "ANCESTOR_STATUS": "1"},
        )
        for values in cases:
            with self.subTest(values=values):
                result, output = self.run_snapshot(**values)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(output, "base=\n")

    def test_pages_generation_is_not_immediately_rechecked(self):
        workflow = yaml.safe_load(
            (ROOT / ".github/workflows/pages.yml").read_text(encoding="utf-8")
        )
        generation = next(
            step
            for step in workflow["jobs"]["deploy"]["steps"]
            if step.get("name") == "Validate and generate site from books.yml"
        )
        self.assertEqual(generation["run"], "make site")

    def test_publish_condition_requires_main_changes_and_successful_gates(self):
        publish = build_workflow()["jobs"]["publish"]
        for gate in ("plan", "book", "check", "build-check"):
            self.assertIn(gate, publish["needs"])
        baseline = {
            "github.event_name": "push",
            "github.ref": "refs/heads/main",
            "needs.plan.result": "success",
            "needs.book.result": "success",
            "needs.check.result": "success",
            "needs.build-check.result": "success",
            "needs.plan.outputs.count": "1",
            "needs.plan.outputs.site_changed": "false",
            "needs.plan.outputs.snapshot_changed": "false",
        }
        self.assertTrue(condition_allows(publish["if"], baseline))
        for gate in ("plan", "book", "check", "build-check"):
            for result in ("success", "failure", "cancelled", "skipped"):
                with self.subTest(gate=gate, result=result):
                    expected = result == "success" or (
                        gate == "book" and result == "skipped"
                    )
                    self.assertEqual(
                        condition_allows(
                            publish["if"], {**baseline, f"needs.{gate}.result": result}
                        ),
                        expected,
                    )
        for event, branch, count, site, snapshot in itertools.product(
            ("push", "workflow_dispatch", "pull_request"),
            ("refs/heads/main", "refs/heads/local-work"),
            ("0", "1"),
            ("false", "true"),
            ("false", "true"),
        ):
            with self.subTest(
                event=event, branch=branch, count=count, site=site, snapshot=snapshot
            ):
                context = {
                    **baseline,
                    "github.event_name": event,
                    "github.ref": branch,
                    "needs.plan.outputs.count": count,
                    "needs.plan.outputs.site_changed": site,
                    "needs.plan.outputs.snapshot_changed": snapshot,
                }
                expected = (
                    event in {"push", "workflow_dispatch"}
                    and branch == "refs/heads/main"
                    and (count != "0" or site == "true" or snapshot == "true")
                )
                self.assertEqual(condition_allows(publish["if"], context), expected)

    def test_snapshot_readme_change_does_not_redeploy_pages(self):
        condition = build_workflow()["jobs"]["pages"]["if"]
        self.assertNotIn("snapshot_changed", condition)

    def test_pdf_artifacts_are_downloaded_into_one_flat_directory(self):
        workflow = build_workflow()
        download = workflow["jobs"]["publish"]["steps"][1]
        self.assertEqual(download["with"]["pattern"], "*-pdf")
        self.assertEqual(download["with"]["path"], "updated-pdfs")
        self.assertIs(download["with"]["merge-multiple"], True)
        upload = workflow["jobs"]["book"]["steps"][-1]
        self.assertEqual(
            upload["with"]["path"],
            "build/${{ matrix.book }}/${{ matrix.book }}.pdf",
        )

    def test_pdf_update_accepts_zero_one_and_multiple_inputs(self):
        cases = (
            (
                {},
                {"alpha.pdf": b"old-a", "beta.pdf": b"old-b"},
                {"alpha.pdf": b"old-a", "beta.pdf": b"old-b"},
                [],
            ),
            (
                {"alpha.pdf": b"new-a"},
                {"beta.pdf": b"old-b"},
                {"alpha.pdf": b"new-a", "beta.pdf": b"old-b"},
                ["alpha"],
            ),
            (
                {"alpha.pdf": b"new-a", "beta.pdf": b"new-b"},
                {},
                {"alpha.pdf": b"new-a", "beta.pdf": b"new-b"},
                ["alpha", "beta"],
            ),
        )
        for updated, existing, expected, required in cases:
            with self.subTest(updated=updated):
                result, snapshot, calls = self.run_pdf_update(updated, existing)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(snapshot, expected)
                self.assertEqual(calls, required)
                self.assertNotIn("*", calls)

    def test_pdf_update_prunes_files_that_are_no_longer_for_site(self):
        result, snapshot, _ = self.run_pdf_update(
            {},
            {"alpha.pdf": b"a", "retired.pdf": b"old"},
            registered=("alpha", "retired"),
            site=("alpha",),
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(snapshot, {"alpha.pdf": b"a"})

    def test_pdf_update_rejects_unknown_slug(self):
        result, _, calls = self.run_pdf_update(
            {"unknown.pdf": b"pdf"},
            {"alpha.pdf": b"old-a", "beta.pdf": b"old-b"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, ["unknown"])

    def test_pdf_update_rejects_empty_artifact_before_slug_validation(self):
        result, _, calls = self.run_pdf_update(
            {"alpha.pdf": b""},
            {"alpha.pdf": b"old-a", "beta.pdf": b"old-b"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, [])
        self.assertIn("PDF artifact is missing or empty", result.stderr)

    def test_pages_requires_snapshot_source_correspondence(self):
        workflow = yaml.safe_load((ROOT / ".github/workflows/pages.yml").read_text())
        step = next(
            step
            for step in workflow["jobs"]["deploy"]["steps"]
            if step.get("id") == "source"
        )
        for snapshot_sha, call_sha, success in (
            ("a" * 40, "a" * 40, True),
            ("b" * 40, "", True),
            ("a" * 40, "b" * 40, False),
            ("invalid", "", False),
            ("", "", False),
            (None, "", False),
        ):
            with (
                self.subTest(snapshot=snapshot_sha, call=call_sha),
                tempfile.TemporaryDirectory() as temporary,
            ):
                root = Path(temporary)
                output = root / "output"
                (root / "pdf-snapshot").mkdir()
                if snapshot_sha is not None:
                    (root / "pdf-snapshot/.source-sha").write_text(snapshot_sha + "\n")
                result = subprocess.run(
                    ["bash", "-euo", "pipefail", "-c", step["run"]],
                    cwd=root,
                    env={
                        **os.environ,
                        "CALL_SHA": call_sha,
                        "GITHUB_OUTPUT": str(output),
                    },
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=10,
                )
                self.assertEqual(result.returncode == 0, success, result.stderr)
                if success:
                    self.assertEqual(output.read_text(), f"sha={snapshot_sha}\n")
                else:
                    self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
