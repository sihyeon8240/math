"""Tests for declarative contents loading and LaTeX generation."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from contents_manifest import expected_files, load_sections, section_filenames


class ContentsManifestTests(unittest.TestCase):
    RECORD = {
        "slug": "sample",
        "title": "Sample Book",
        "author": "Sample Author",
        "version": "1.2.3",
    }

    def fixture(self, root: Path) -> Path:
        book = root / "book"
        chapter = book / "chapters/01-start"
        chapter.mkdir(parents=True)
        (book / "chapters.yml").write_text(
            "schema_version: 1\nchapters:\n  - slug: start\n    title: Start\n",
            encoding="utf-8",
        )
        (chapter / "sections.yml").write_text(
            "schema_version: 1\nsections:\n"
            "  - slug: first\n    title: First\n"
            "    split: 2\n",
            encoding="utf-8",
        )
        (book / "book.tex").write_text(
            "before\n% BEGIN GENERATED METADATA\nold metadata\n"
            "% END GENERATED METADATA\n% BEGIN GENERATED CHAPTERS\nold\n"
            "% END GENERATED CHAPTERS\n\\backmatter\n"
            "% BEGIN GENERATED APPENDICES\nold appendix\n"
            "% END GENERATED APPENDICES\nafter\n",
            encoding="utf-8",
        )
        for part in "ab":
            (chapter / f"01-first-{part}.tex").write_text("body\n", encoding="utf-8")
        return book

    def test_render_uses_manifest_order_titles_and_split_count(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            book = self.fixture(Path(temporary))
            rendered = expected_files(book, book=self.RECORD)
            self.assertIn(
                r"\include{chapters/01-start/index}", rendered[book / "book.tex"]
            )
            index = rendered[book / "chapters/01-start/index.tex"]
            self.assertIn(r"\chapter{Start}", index)
            self.assertEqual(index.count(r"\section{First}"), 1)
            self.assertLess(
                index.index("01-first-a.tex"), index.index("01-first-b.tex")
            )

    def test_metadata_is_rendered_from_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            book_dir = self.fixture(Path(temporary))
            entry = expected_files(book_dir, book=self.RECORD)[book_dir / "book.tex"]

            self.assertIn(r"\newcommand{\name}{Sample Author}", entry)
            self.assertIn(r"\newcommand{\displaytitle}{Sample Book}", entry)
            self.assertIn(r"\newcommand{\version}{1.2.3}", entry)
            self.assertIn(r"\newcommand{\slug}{sample}", entry)

    def test_appendices_render_after_backmatter(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            book = self.fixture(Path(temporary))
            appendix = book / "appendices/01-tables"
            appendix.mkdir(parents=True)
            (book / "chapters.yml").write_text(
                (book / "chapters.yml").read_text()
                + "appendices:\n  - slug: tables\n    title: Tables\n"
            )
            (appendix / "sections.yml").write_text(
                "schema_version: 1\nsections:\n  - slug: values\n    title: Values\n"
            )
            (appendix / "01-values.tex").write_text("body\n")

            rendered = expected_files(book, book=self.RECORD)
            entry = rendered[book / "book.tex"]
            self.assertLess(
                entry.index("backmatter"), entry.index("appendices/01-tables")
            )
            index = rendered[appendix / "index.tex"]
            self.assertIn("chapter{Tables}", index)
            self.assertIn("appendices/01-tables/01-values.tex", index)

    def test_existing_entry_contents_are_ignored(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            book = self.fixture(Path(temporary))
            path = book / "book.tex"
            path.write_text("hand-edited entry\n", encoding="utf-8")
            rendered = expected_files(book, book=self.RECORD)[path]
            self.assertNotIn("hand-edited entry", rendered)
            self.assertTrue(rendered.startswith("% Generated from"))

    def test_split_count_26_ends_at_z(self) -> None:
        filenames = section_filenames(1, {"slug": "topic", "split": 26})
        self.assertEqual(len(filenames), 26)
        self.assertEqual(filenames[-1], "01-topic-z.tex")

    def test_split_must_fit_lowercase_suffixes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            book = self.fixture(Path(temporary))
            path = book / "chapters/01-start/sections.yml"
            valid = path.read_text()
            for value in (1, 27, True, "two"):
                with self.subTest(value=value):
                    path.write_text(valid.replace("split: 2", f"split: {value}"))
                    with self.assertRaisesRegex(ValueError, "integer from 2 to 26"):
                        load_sections(path.parent)

    def test_titles_must_be_single_line_with_balanced_braces(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            book = self.fixture(Path(temporary))
            path = book / "chapters/01-start/sections.yml"
            original = path.read_text()
            for title in ("Broken } title", r'"two\nlines"'):
                with self.subTest(title=title):
                    path.write_text(original.replace("title: First", f"title: {title}"))
                    with self.assertRaisesRegex(ValueError, "balanced single-line"):
                        load_sections(path.parent)

    def test_orphan_and_manual_section_declarations_fail(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            book = self.fixture(Path(temporary))
            orphan = book / "chapters/01-start/02-orphan.tex"
            orphan.write_text("body\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "orphan section source"):
                expected_files(book, book=self.RECORD)
            orphan.unlink()
            source = book / "chapters/01-start/01-first-a.tex"
            source.write_text(r"\section{Wrong}" + "\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "belong in sections.yml"):
                expected_files(book, book=self.RECORD)


if __name__ == "__main__":
    unittest.main()
