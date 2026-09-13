"""Tests for Lean coverage source accounting."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import lean_coverage


class LeanCoverageTests(unittest.TestCase):
    def test_comments_are_excluded_from_theorem_total(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "books/sample/chapter.tex"
            source.parent.mkdir(parents=True)
            source.write_text(
                "% \\begin{theorem}\n\\begin{lemma}Real.\\end{lemma}\n",
                encoding="utf-8",
            )
            with mock.patch.object(
                lean_coverage, "load_proof_index", return_value=([], [])
            ):
                metrics = lean_coverage.book_lean_metrics("sample", root)
            self.assertEqual(metrics["total"], 1)

    def test_verified_count_cannot_exceed_theorem_total(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "books/sample").mkdir(parents=True)
            proofs = [{"book": "sample"}]
            with mock.patch.object(
                lean_coverage, "load_proof_index", return_value=([], proofs)
            ):
                with self.assertRaisesRegex(ValueError, "only 0 theorem"):
                    lean_coverage.book_lean_metrics("sample", root)


if __name__ == "__main__":
    unittest.main()
