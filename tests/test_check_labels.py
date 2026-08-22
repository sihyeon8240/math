"""Behavior tests for label policy validation."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CHECK_LABELS = ROOT / "scripts/check-labels.py"


class CheckLabelsTests(unittest.TestCase):
    def run_checker(self, files: dict[str, str]) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paths = []
            for relative, contents in files.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(contents, encoding="utf-8")
                paths.append(path)
            return subprocess.run(
                [sys.executable, str(CHECK_LABELS), *map(str, paths)],
                capture_output=True,
                text=True,
                check=False,
            )

    def test_valid_modern_and_template_labels_pass(self) -> None:
        result = self.run_checker(
            {
                "books/linear-algebra/chapter.tex": (
                    "\label{la:thm:basis}\n\label{la:ax:choice}"
                ),
                "common/templates/chapter.tex": r"\label{xx:ch:introduction}",
            }
        )
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_duplicate_empty_whitespace_and_prefix_collision_fail(self) -> None:
        result = self.run_checker(
            {
                "books/linear-algebra/a.tex": "\\label{la:thm:one}\n\\label{}\n",
                "books/linear-algebra/b.tex": (
                    "\\label{la:thm:one}\n"
                    "\\label{la:thm:bad label}\n"
                    "\\label{an:thm:collision}\n"
                ),
            }
        )
        self.assertEqual(result.returncode, 1)
        expected_messages = (
            "duplicate label",
            "empty label",
            "whitespace in label",
            "prefix collision",
        )
        for message in expected_messages:
            self.assertIn(message, result.stderr)

    def test_legacy_labels_warn_without_failing(self) -> None:
        result = self.run_checker({"books/linear-algebra/a.tex": r"\label{old-style}"})
        self.assertEqual(result.returncode, 0)
        self.assertIn(
            "a.tex:1: warning: legacy label 'old-style' does not follow "
            "<book>:<kind>:<description>",
            result.stderr,
        )
        self.assertIn("1 legacy labels", result.stderr)


if __name__ == "__main__":
    unittest.main()
