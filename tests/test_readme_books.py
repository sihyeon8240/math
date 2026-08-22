"""README book-table generation tests."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

spec = importlib.util.spec_from_file_location(
    "readme_generator", REPO_ROOT / "scripts" / "generate-readme-books.py"
)
assert spec and spec.loader
readme_generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(readme_generator)


class ReadmeBooksTests(unittest.TestCase):
    def manifest(self) -> dict:
        return {
            "books": [
                {
                    "slug": "alpha",
                    "title": "Alpha | Complete",
                    "short_title": "A",
                    "build": False,
                    "check": False,
                    "release": False,
                    "site": False,
                },
                {
                    "slug": "beta",
                    "title": "Beta",
                    "build": True,
                    "check": True,
                    "release": True,
                    "site": True,
                },
            ]
        }

    def readme(self, body: str = "old table") -> str:
        return (
            "# Before\r\n\r\n"
            f"{readme_generator.BEGIN_MARKER}{body}"
            f"{readme_generator.END_MARKER}"
            "\r\n\r\nAfter\r\n"
        )

    def write_books(self, root: Path) -> None:
        for slug, title in (("alpha", "First"), ("beta", "Second")):
            directory = root / slug
            chapter = directory / "chapters" / "01-first" / "index.tex"
            chapter.parent.mkdir(parents=True)
            (directory / "book.tex").write_text(
                "\\include{chapters/01-first/index}\n", encoding="utf-8"
            )
            chapter.write_text(f"\\chapter{{{title}}}\n", encoding="utf-8")
            (directory / "references.bib").write_text(
                f"@book{{source,\n  author = {{Author, Ada}},\n"
                f"  title = {{{title} Reference}},\n  publisher = {{Publisher}},\n}}\n",
                encoding="utf-8",
            )
            (directory / "README.md").write_text(
                "# Book\n\n"
                f"{readme_generator.DETAILS_BEGIN_MARKER}\n\nold\n\n"
                f"{readme_generator.DETAILS_END_MARKER}\n",
                encoding="utf-8",
            )

    def test_render_uses_normalized_order_title_and_all_books(self) -> None:
        table = readme_generator.render_books_table(self.manifest())
        self.assertLess(table.index("alpha"), table.index("beta"))
        self.assertIn("Alpha \\| Complete", table)
        self.assertNotIn("| A |", table)
        self.assertIn("make books BOOK=alpha", table)
        self.assertIn("make books BOOK=beta", table)

    def test_render_is_deterministic(self) -> None:
        self.assertEqual(
            readme_generator.render_books_table(self.manifest()),
            readme_generator.render_books_table(self.manifest()),
        )

    def test_replacement_preserves_everything_outside_markers(self) -> None:
        current = self.readme("\r\nOLD\r\n")
        updated = readme_generator.replace_generated_books(current, "NEW")
        begin_end = current.index(readme_generator.BEGIN_MARKER) + len(
            readme_generator.BEGIN_MARKER
        )
        end = current.index(readme_generator.END_MARKER)
        self.assertEqual(updated[:begin_end], current[:begin_end])
        self.assertEqual(
            updated[updated.index(readme_generator.END_MARKER) :], current[end:]
        )

    def test_chapter_list_comes_from_book_assembly(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.write_books(root)
            self.assertEqual(
                readme_generator.assembly_titles(root / "alpha"), (["First"], [])
            )
            readme = (root / "alpha" / "README.md").read_text(encoding="utf-8")
            updated = readme_generator.replace_generated_details(
                readme, "1. First", root / "alpha" / "README.md"
            )
            self.assertIn("\n\n1. First\n\n", updated)

    def test_texorpdfstring_uses_unicode_plain_text_argument(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.write_books(root)
            chapter = root / "alpha" / "chapters" / "01-first" / "index.tex"
            chapter.write_text(
                "\\chapter{Construction of \\texorpdfstring{$\\mathbb{R}$}{ℝ}}\n",
                encoding="utf-8",
            )
            self.assertEqual(
                readme_generator.assembly_titles(root / "alpha"),
                (["Construction of ℝ"], []),
            )

    def test_details_include_appendices_references_and_build_help(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.write_books(root)
            appendix = root / "alpha" / "appendices" / "real" / "index.tex"
            appendix.parent.mkdir(parents=True)
            appendix.write_text(
                "\\chapter{Appendix: Construction of "
                "\\texorpdfstring{$\\mathbb{R}$}{ℝ}}\n",
                encoding="utf-8",
            )
            book = root / "alpha" / "book.tex"
            book.write_text(
                book.read_text(encoding="utf-8") + "\\include{appendices/real/index}\n",
                encoding="utf-8",
            )
            details = readme_generator.render_book_details(root / "alpha", "alpha")
            self.assertIn("Appendix: Construction of ℝ", details)
            self.assertIn("Ada Author, *First Reference*, Publisher.", details)
            self.assertIn("make books BOOK=alpha", details)

    def test_all_bibliography_entry_types_are_rendered(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "references.bib"
            path.write_text(
                "@book{one, author={Author, Ada}, title={Book}, publisher={Press}}\n"
                "@article{two, author={Writer, Bea}, title={Paper}, "
                "journaltitle={Journal}, year={2026}}\n",
                encoding="utf-8",
            )
            entries = readme_generator.bibliography_entries(path)
            self.assertEqual(len(entries), 2)
            self.assertEqual(
                readme_generator.render_reference(entries[1]),
                "Bea Writer, *Paper*, Journal, 2026.",
            )

    def test_generate_and_check_modes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "README.md"
            books_dir = root / "books"
            path.write_bytes(self.readme().encode("utf-8"))
            self.write_books(books_dir)
            stale = path.read_bytes()
            self.assertEqual(
                readme_generator.generate(
                    check=True,
                    readme_path=path,
                    manifest=self.manifest(),
                    books_dir=books_dir,
                ),
                1,
            )
            self.assertEqual(path.read_bytes(), stale)
            self.assertEqual(
                readme_generator.generate(
                    readme_path=path, manifest=self.manifest(), books_dir=books_dir
                ),
                0,
            )
            fresh = path.read_bytes()
            self.assertEqual(
                readme_generator.generate(
                    check=True,
                    readme_path=path,
                    manifest=self.manifest(),
                    books_dir=books_dir,
                ),
                0,
            )
            self.assertEqual(path.read_bytes(), fresh)

    def test_root_scope_does_not_require_book_files(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "README.md"
            path.write_bytes(self.readme().encode("utf-8"))
            self.assertEqual(
                readme_generator.generate(
                    readme_path=path,
                    manifest=self.manifest(),
                    books_dir=root / "missing",
                    scope="root",
                ),
                0,
            )

    def test_single_book_scope_updates_only_selected_book(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            books_dir = root / "books"
            self.write_books(books_dir)
            beta = books_dir / "beta" / "README.md"
            beta_before = beta.read_bytes()
            self.assertEqual(
                readme_generator.generate(
                    manifest=self.manifest(),
                    books_dir=books_dir,
                    scope="books",
                    book="alpha",
                ),
                0,
            )
            self.assertEqual(beta.read_bytes(), beta_before)
            self.assertNotIn("old", (books_dir / "alpha" / "README.md").read_text())

    def test_unknown_single_book_fails(self) -> None:
        with self.assertRaisesRegex(ValueError, "not registered"):
            readme_generator.generate(
                manifest=self.manifest(), scope="books", book="missing"
            )

    def test_missing_begin_marker_fails(self) -> None:
        with self.assertRaisesRegex(ValueError, "BEGIN.*found 0"):
            readme_generator.replace_generated_books(
                readme_generator.END_MARKER, "table"
            )

    def test_missing_end_marker_fails(self) -> None:
        with self.assertRaisesRegex(ValueError, "END.*found 0"):
            readme_generator.replace_generated_books(
                readme_generator.BEGIN_MARKER, "table"
            )

    def test_duplicate_markers_fail(self) -> None:
        cases = (
            readme_generator.BEGIN_MARKER * 2 + readme_generator.END_MARKER,
            readme_generator.BEGIN_MARKER + readme_generator.END_MARKER * 2,
        )
        for readme in cases:
            with (
                self.subTest(readme=readme),
                self.assertRaisesRegex(ValueError, "exactly one"),
            ):
                readme_generator.replace_generated_books(readme, "table")

    def test_reversed_markers_fail(self) -> None:
        with self.assertRaisesRegex(ValueError, "wrong order"):
            readme_generator.replace_generated_books(
                readme_generator.END_MARKER + readme_generator.BEGIN_MARKER, "table"
            )


if __name__ == "__main__":
    unittest.main()
