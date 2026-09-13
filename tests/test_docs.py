"""Regression checks for stale authoring guidance and broken local links."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
spec = importlib.util.spec_from_file_location(
    "check_docs", ROOT / "scripts/check-docs.py"
)
assert spec and spec.loader
docs = importlib.util.module_from_spec(spec)
spec.loader.exec_module(docs)


class DocumentationTests(unittest.TestCase):
    def test_links_detect_missing_paths_anchors_and_references(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "target.md").write_text("# Target\n\n## Details\n")
            source = root / "README.md"
            source.write_text(
                "[ok](target.md#details)\n[bad](target.md#old)\n"
                "[`gone`](gone.md)\n[ref][missing]\n"
                "[valid][target]\n[target]: target.md#target\n"
                "[web](https://example.invalid)\n"
                "```md\n[example](absent.md)\n```\n"
                "`[example](absent.md)`\n"
            )
            errors = docs.link_errors(source, root)
            self.assertEqual(len(errors), 3, errors)
            self.assertIn("missing heading anchor: target.md#old", errors)
            self.assertIn("missing link target: gone.md", errors)
            self.assertIn("undefined link reference: missing", errors)

    def test_heading_slug_matches_code_punctuation_and_duplicates(self):
        self.assertEqual(
            docs.anchors(
                "## Displayed justifications with `\\by`\n## Repeat\n## Repeat\n"
            ),
            {"displayed-justifications-with-by", "repeat", "repeat-1"},
        )

    def test_url_encoded_paths_and_self_anchors(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "other file.md").write_text("# Other\n")
            source = root / "README.md"
            source.write_text("# Here\n[x](other%20file.md#other)\n[y](#here)\n")
            self.assertEqual(docs.link_errors(source, root), [])

    def test_snapshot_exception_is_limited_to_its_publication_pdf_directory(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / ".github").mkdir()
            source = root / ".github/generated-pdfs-README.md"
            source.write_text("[PDF](pdf/)\n[bad](absent.md)\n")
            self.assertEqual(
                docs.link_errors(source, root), ["missing link target: absent.md"]
            )

    def test_environment_check_detects_drift_in_both_directions(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "docs").mkdir()
            (root / "common/styles").mkdir(parents=True)
            (root / "docs/writing-guide.md").write_text(
                "### Theorem environments\n\n"
                "The public environments are `theorem`, `exercise`, and `proof`. Use them.\n"
            )
            (root / "common/styles/textbook-theorems.sty").write_text(
                "\\RequirePackage{amsthm}\n"
                "\\newtheorem{theorem}{Theorem}\n"
                "\\newtheorem*{remark}{Remark}\n"
                "% \\newtheorem{exercise}{Exercise}\n"
            )
            self.assertEqual(
                docs.environment_errors(root),
                [
                    "documented environment is undefined: exercise",
                    "shared environment is undocumented: remark",
                ],
            )


if __name__ == "__main__":
    unittest.main()
