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

    def test_only_linked_tex_results_count_once(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "books/sample/chapter.tex"
            source.parent.mkdir(parents=True)
            source.write_text(
                "\\begin{theorem}\\label{s:thm:first}\\label{s:thm:alias}"
                "Real.\\end{theorem}\n"
                "\\begin{lemma}Unlabeled.\\end{lemma}\n"
                "\\begin{proposition}\\label{s:prop:unlinked}Real.\\end{proposition}\n"
                "\\begin{corollary}\\label{s:cor:other}Real.\\end{corollary}\n"
                "\\begin{definition}\\label{s:thm:def}Definition.\\end{definition}\n"
                "\\label{s:thm:outside}\n"
                "% \\begin{theorem}\\label{s:thm:comment}\\end{theorem}\n"
                "\\begin{lean}\\begin{theorem}\\label{s:thm:code}"
                "\\end{theorem}\\end{lean}\n",
                encoding="utf-8",
            )
            proofs = [
                {"book": "sample", "id": label, "declaration": f"Sample.proof{i}"}
                for i, label in enumerate(
                    [
                        "s:thm:first",
                        "s:thm:first",
                        "s:thm:alias",
                        "s:thm:lean-only",
                        "s:thm:def",
                        "s:thm:outside",
                        "s:thm:comment",
                        "s:thm:code",
                    ]
                )
            ]
            proofs.append(
                {"book": "other", "id": "s:cor:other", "declaration": "Other.proof"}
            )
            proofs.append({"book": "sample", "id": "s:prop:unlinked"})
            with mock.patch.object(
                lean_coverage, "load_proof_index", return_value=([], proofs)
            ):
                metrics = lean_coverage.book_lean_metrics("sample", root)
            self.assertEqual(metrics, {"verified": 1, "total": 4, "percentage": 25.0})

    def test_multiple_books_share_one_index_without_stale_global_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for slug in ("alpha", "beta"):
                source = root / "books" / slug / "chapter.tex"
                source.parent.mkdir(parents=True)
                source.write_text(
                    f"\\begin{{theorem}}\\label{{{slug}:thm:result}}"
                    "Result.\\end{theorem}\n",
                    encoding="utf-8",
                )
            proofs = [
                {
                    "book": "alpha",
                    "id": "alpha:thm:result",
                    "declaration": "Alpha.result",
                }
            ]
            with mock.patch.object(
                lean_coverage, "load_proof_index", return_value=([], proofs)
            ) as load:
                registered = lean_coverage.registered_results(root)
                alpha = lean_coverage.book_lean_metrics(
                    "alpha", root, registered=registered
                )
                beta = lean_coverage.book_lean_metrics(
                    "beta", root, registered=registered
                )
                load.assert_called_once_with(root)
            self.assertEqual(alpha, {"verified": 1, "total": 1, "percentage": 100.0})
            self.assertEqual(beta, {"verified": 0, "total": 1, "percentage": 0.0})
            with mock.patch.object(
                lean_coverage, "load_proof_index", return_value=([], [])
            ):
                self.assertEqual(
                    lean_coverage.book_lean_metrics("alpha", root)["verified"], 0
                )

    def test_invalid_index_is_not_hidden_by_batch_loading(self) -> None:
        with mock.patch.object(
            lean_coverage, "load_proof_index", return_value=(["broken proof shard"], [])
        ):
            with self.assertRaisesRegex(ValueError, "broken proof shard"):
                lean_coverage.registered_results()

    def test_registered_results_without_theorems_keep_zero_percentage(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "books/sample").mkdir(parents=True)
            proofs = [{"book": "sample"}]
            with mock.patch.object(
                lean_coverage, "load_proof_index", return_value=([], proofs)
            ):
                metrics = lean_coverage.book_lean_metrics("sample", root)
            self.assertEqual(metrics, {"verified": 0, "total": 0, "percentage": 0.0})


if __name__ == "__main__":
    unittest.main()
