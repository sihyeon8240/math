"""Behavior tests for strict release packaging and artifact preservation."""

from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class PackageBookTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="math package ")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        for name in ("package-book.sh", "check-log.py"):
            shutil.copy2(ROOT / "scripts" / name, scripts / name)
        (scripts / "books.py").write_text(
            "import sys\n"
            "if sys.argv[1:] == ['require', 'alpha']: raise SystemExit(0)\n"
            "if sys.argv[1:] == ['version', 'alpha']: print('1.2.3')\n"
            "else: raise SystemExit(2)\n",
            encoding="utf-8",
        )
        build = self.root / "build/alpha"
        build.mkdir(parents=True)
        self.pdf = build / "book.pdf"
        self.pdf.write_bytes(b"%PDF-1.5\npackaged content\n")
        self.log = build / "book.log"
        self.log.write_text(
            "Output written on book.pdf (1 page, 123 bytes).\n", encoding="utf-8"
        )
        self.output = self.root / "release"
        self.target = self.output / "alpha-v1.2.3.pdf"

    def package(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(self.root / "scripts/package-book.sh"), "alpha", str(self.output)],
            cwd=self.root,
            env={**os.environ, "PYTHON": sys.executable},
            capture_output=True,
            text=True,
            check=False,
            timeout=10,
        )

    def test_clean_build_creates_versioned_pdf_and_correct_checksum(self) -> None:
        result = self.package()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.target.read_bytes(), self.pdf.read_bytes())
        self.assertEqual(
            (self.output / "SHA256SUMS").read_text(),
            f"{hashlib.sha256(self.pdf.read_bytes()).hexdigest()}  {self.target.name}\n",
        )
        self.assertEqual(
            {path.name for path in self.output.iterdir()},
            {self.target.name, "SHA256SUMS"},
        )

    def test_existing_artifacts_are_preserved(self) -> None:
        self.output.mkdir()
        self.target.write_bytes(b"existing PDF")
        sums = self.output / "SHA256SUMS"
        sums.write_text("existing checksums\n")
        result = self.package()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("refusing to overwrite", result.stderr)
        self.assertEqual(self.target.read_bytes(), b"existing PDF")
        self.assertEqual(sums.read_text(), "existing checksums\n")

    def test_overfull_log_prevents_release_pdf(self) -> None:
        self.log.write_text(
            "Overfull \\hbox (1.0pt too wide) detected at line 1\n"
            + self.log.read_text()
        )
        result = self.package()
        self.assertEqual(result.returncode, 1)
        self.assertIn("error: overfull box", result.stderr)
        self.assertFalse(self.output.exists())

    def test_missing_pdf_or_log_fails_without_creating_artifacts(self) -> None:
        for path in (self.pdf, self.log):
            with self.subTest(path=path.name):
                original = path.read_bytes()
                path.unlink()
                try:
                    result = self.package()
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("missing", result.stderr)
                    self.assertFalse(self.output.exists())
                finally:
                    path.write_bytes(original)


if __name__ == "__main__":
    unittest.main()
