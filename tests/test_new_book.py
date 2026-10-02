"""Textbook scaffold creation and failure rollback."""

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


class NewBookTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        scripts = self.root / "scripts"
        templates = self.root / "common/templates"
        scripts.mkdir(parents=True)
        templates.mkdir(parents=True)
        (self.root / "books").mkdir()
        (self.root / "books.yml").write_text("books: []\n", encoding="utf-8")
        shutil.copy2(ROOT / "scripts/new-book.sh", scripts / "new-book.sh")
        for name, content in {
            "book.tex": "book\n",
            "chapter.tex": "chapter xx:ch:start\n",
            "section.tex": "section xx:sec:first\n",
            "chapters.yml": "chapters\n",
            "sections.yml": "sections\n",
            "references.bib": "",
            "formalization.md": "# Formalization boundary\n",
        }.items():
            (templates / name).write_text(content, encoding="utf-8")
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
        (scripts / "generate-contents.py").write_text("", encoding="utf-8")

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
            timeout=30,
        )

    def test_success_creates_minimal_scaffold(self) -> None:
        result = self.run_new()
        target = self.root / "books/new-book"
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((target / "chapters/01-introduction/index.tex").is_file())
        self.assertFalse((target / "frontmatter").exists())
        self.assertFalse((target / "metadata.tex").exists())
        self.assertFalse((target / "local-style.sty").exists())
        self.assertTrue((target / "references.bib").is_file())
        self.assertEqual(
            (target / "formalization.md").read_text(),
            "# Formalization boundary\n",
        )
        self.assertIn(
            "nb:sec:first",
            (target / "chapters/01-introduction/01-first-section.tex").read_text(),
        )
        self.assertFalse((target / "README.md").exists())

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
