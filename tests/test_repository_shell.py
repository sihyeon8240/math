"""Integration tests for repository maintenance shell scripts."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class CleanTests(unittest.TestCase):
    def test_clean_removes_only_build_contents(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(ROOT / "scripts/clean.sh", scripts / "clean.sh")
            (root / "build/nested").mkdir(parents=True)
            (root / "build/nested/output.pdf").write_bytes(b"pdf")
            outside = root / "keep.txt"
            outside.write_text("keep", encoding="utf-8")

            result = subprocess.run(
                [str(scripts / "clean.sh")],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(list((root / "build").iterdir()), [])
            self.assertEqual(outside.read_text(encoding="utf-8"), "keep")


class NewBookTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        scripts = self.root / "scripts"
        templates = self.root / "common/templates"
        scripts.mkdir(parents=True)
        (templates / "frontmatter").mkdir(parents=True)
        (self.root / "books").mkdir()
        (self.root / "books.yml").write_text("books: []\n", encoding="utf-8")
        shutil.copy2(ROOT / "scripts/new-book.sh", scripts / "new-book.sh")
        for name, content in {
            "book.tex": "book\n",
            "metadata.tex": "__TITLE__ __SLUG__\n",
            "README.md": "# __BOOK_TITLE__ (__BOOK_SLUG__)\n",
            "chapter.tex": "chapter xx:ch:start\n",
            "section.tex": "section xx:sec:first\n",
            "local-style.sty": "style\n",
            "references.bib": "",
        }.items():
            (templates / name).write_text(content, encoding="utf-8")
        (templates / "frontmatter/title-and-copyright.tex").write_text(
            "title\n", encoding="utf-8"
        )
        (templates / "frontmatter/preface.tex").write_text(
            "preface\n", encoding="utf-8"
        )
        (scripts / "books.py").write_text(
            textwrap.dedent("""\
            import os
            import sys
            if sys.argv[1] == "add" and os.environ.get("FAIL_ADD") == "1":
                raise SystemExit(1)
            if sys.argv[1] == "label-prefix":
                print("nb")
            """),
            encoding="utf-8",
        )
        (scripts / "generate-readme-books.py").write_text("", encoding="utf-8")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def run_new(
        self, slug: str = "new-book", **environment: str
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(self.root / "scripts/new-book.sh"), slug, "New Book"],
            cwd=self.root,
            env={**os.environ, "PYTHON": sys.executable, **environment},
            capture_output=True,
            text=True,
            check=False,
        )

    def test_success_creates_scaffold_and_substitutes_metadata(self) -> None:
        result = self.run_new()
        target = self.root / "books/new-book"
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((target / "chapters/01-introduction/index.tex").is_file())
        self.assertTrue((target / "frontmatter/title-and-copyright.tex").is_file())
        self.assertTrue((target / "frontmatter/preface.tex").is_file())
        self.assertTrue((target / "references.bib").is_file())
        self.assertIn(
            "nb:ch:start", (target / "chapters/01-introduction/index.tex").read_text()
        )
        self.assertEqual(
            (target / "metadata.tex").read_text(encoding="utf-8"),
            "New Book new-book\n",
        )

    def test_existing_target_is_preserved(self) -> None:
        target = self.root / "books/new-book"
        target.mkdir()
        marker = target / "keep"
        marker.write_text("keep", encoding="utf-8")
        result = self.run_new()
        self.assertEqual(result.returncode, 1)
        self.assertTrue(marker.is_file())

    def test_failure_after_creation_removes_partial_scaffold(self) -> None:
        result = self.run_new(FAIL_ADD="1")
        self.assertEqual(result.returncode, 1)
        self.assertFalse((self.root / "books/new-book").exists())
        self.assertIn("creation failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
