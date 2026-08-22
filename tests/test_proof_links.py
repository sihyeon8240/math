"""Regression tests for LaTeX-to-Lean proof linkage."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "check_proof_links", ROOT / "scripts/check-proof-links.py"
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class ProofLinkTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        tex = self.root / "books/sample/chapters/01-start/01-result.tex"
        tex.parent.mkdir(parents=True)
        tex.write_text(
            r"\begin{theorem}\label{sa:thm:result}Result.\end{theorem}"
            "\n"
            r"\leanverified{sa:thm:result}"
            "\n",
            encoding="utf-8",
        )
        self.write_yaml(
            "books.yml",
            {
                "schema_version": 1,
                "books": [
                    {
                        "slug": "sample",
                        "label_prefix": "sa",
                        "lean_module": "Sample",
                    }
                ],
            },
        )
        self.entry = {
            "id": "sa:thm:result",
            "tex": "chapters/01-start/01-result.tex",
            "declaration": "Textbooks.Sample.result",
            "foundations": ["set-theory"],
        }

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write_yaml(self, path: str, data: object) -> None:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(yaml.safe_dump(data, sort_keys=False), encoding="utf-8")

    def errors(self, entries: list[object]) -> list[str]:
        self.write_yaml(
            "proof-index/sample/01-start.yml",
            {
                "book": "sample",
                "chapter": "01-start",
                "proofs": entries,
            },
        )
        return MODULE.validate_index(self.root)[0]

    def test_valid_entry(self) -> None:
        self.assertEqual(self.errors([self.entry]), [])

    def test_missing_tex_marker_is_rejected(self) -> None:
        self.entry["id"] = "sa:thm:other"
        errors = self.errors([self.entry])
        self.assertTrue(any("label is absent" in error for error in errors))
        self.assertTrue(
            any("verification marker is absent" in error for error in errors)
        )

    def test_duplicate_declaration_is_rejected(self) -> None:
        duplicate = dict(self.entry, id="sa:lem:result")
        errors = self.errors([self.entry, duplicate])
        self.assertTrue(any("duplicate Lean declaration" in error for error in errors))

    def test_parent_path_is_rejected(self) -> None:
        self.entry["tex"] = "../outside.tex"
        errors = self.errors([self.entry])
        self.assertTrue(any("unsafe TeX path" in error for error in errors))

    def test_shard_owned_entry_fields_are_rejected(self) -> None:
        self.entry["book"] = "sample"
        errors = self.errors([self.entry])
        self.assertTrue(any("shard-owned fields" in error for error in errors))

    def test_tex_path_outside_shard_chapter_is_rejected(self) -> None:
        self.entry["tex"] = "chapters/02-other/01-result.tex"
        errors = self.errors([self.entry])
        self.assertTrue(any("outside shard chapter" in error for error in errors))

    def test_unregistered_tex_marker_is_rejected(self) -> None:
        tex = self.root / "books/sample/chapters/01-start/02-other.tex"
        tex.write_text(
            r"\leanverified{sa:thm:other}" "\n",
            encoding="utf-8",
        )
        errors = self.errors([self.entry])
        self.assertTrue(
            any("unregistered Lean verification marker" in error for error in errors)
        )

    def test_book_prefix_and_namespace_are_enforced(self) -> None:
        self.entry["id"] = "xx:thm:result"
        self.entry["declaration"] = "Textbooks.Other.result"
        errors = self.errors([self.entry])
        self.assertTrue(any("does not use book prefix" in error for error in errors))
        self.assertTrue(any("outside the book namespace" in error for error in errors))

    def test_unreachable_lean_source_is_rejected(self) -> None:
        self.write_yaml(
            "books.yml",
            {
                "schema_version": 1,
                "books": [
                    {
                        "slug": "sample",
                        "lean_module": "Sample",
                    }
                ],
            },
        )
        lean = self.root / "lean"
        module = lean / "Textbooks/Sample"
        module.mkdir(parents=True)
        (lean / "Textbooks.lean").write_text(
            "import Textbooks.Sample.All\n", encoding="utf-8"
        )
        (module / "All.lean").write_text("", encoding="utf-8")
        (module / "Orphan.lean").write_text("", encoding="utf-8")
        errors = MODULE.validate_import_boundaries(self.root)
        self.assertTrue(
            any("not reachable from Textbooks" in error for error in errors)
        )

    def test_cross_book_import_is_rejected(self) -> None:
        self.write_yaml(
            "books.yml",
            {
                "schema_version": 1,
                "books": [
                    {
                        "slug": "analysis",
                        "lean_module": "MathematicalAnalysis",
                    },
                    {
                        "slug": "algebra",
                        "lean_module": "LinearAlgebra",
                    },
                ],
            },
        )
        textbooks = self.root / "lean/Textbooks"
        for module in ("MathematicalAnalysis", "LinearAlgebra"):
            (textbooks / module).mkdir(parents=True)
        source = textbooks / "MathematicalAnalysis/Chapter01.lean"
        source.write_text("import Textbooks.LinearAlgebra.All\n", encoding="utf-8")
        errors = MODULE.validate_import_boundaries(self.root)
        self.assertTrue(any("cross-book import" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
