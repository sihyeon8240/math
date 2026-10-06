"""Behavior tests for the informational repository report."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location(
    "repository_report", ROOT / "scripts/repository-report.py"
)
assert spec and spec.loader
report = importlib.util.module_from_spec(spec)
spec.loader.exec_module(report)


class RepositoryReportTests(unittest.TestCase):
    def run_main(self) -> tuple[int, str]:
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            result = report.main()
        return result, output.getvalue()

    def test_report_reuses_source_text_for_statistics_and_coverage(self) -> None:
        book = report.load_manifest()["books"][0]
        registered = report.registered_results()
        original = Path.read_text
        reads = []

        def tracked(path, *args, **kwargs):
            if path.suffix == ".tex":
                reads.append(path)
            return original(path, *args, **kwargs)

        with mock.patch.object(Path, "read_text", tracked):
            result = report.inspect(book, registered)
        self.assertEqual(len(reads), len(set(reads)))
        self.assertGreater(result["sections"], 0)
        labels = registered.get(book["slug"], set())
        expected_verified = sum(
            bool(group & labels)
            for path in reads
            for group in report.theorem_label_groups(original(path))
        )
        self.assertEqual(result["lean_verified"], expected_verified)

    def test_empty_manifest_produces_a_complete_report(self) -> None:
        with mock.patch.object(report, "load_manifest", return_value={"books": []}):
            result, output = self.run_main()

        self.assertEqual(result, 0)
        self.assertIn("Books: 0", output)
        self.assertIn("No chapters found", output)
        self.assertIn("This command never modifies files", output)

    def test_failure_is_reported_without_turning_health_report_into_a_gate(
        self,
    ) -> None:
        with mock.patch.object(
            report, "load_manifest", side_effect=ValueError("broken manifest")
        ):
            result, output = self.run_main()

        self.assertEqual(result, 0)
        self.assertIn("warning: report is incomplete: broken manifest", output)


if __name__ == "__main__":
    unittest.main()
