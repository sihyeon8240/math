"""Regression tests for manifest-owned Lean aggregation."""

from __future__ import annotations

import contextlib
import importlib.util
import io
import sys
import tempfile
import unittest
from pathlib import Path

from test_support import book_record, manifest_document, write_yaml

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))

from lean_manifest import expected_files

ROOT = Path(__file__).resolve().parent.parent

SPEC = importlib.util.spec_from_file_location(
    "generate_lean", ROOT / "scripts/generate-lean.py"
)
assert SPEC and SPEC.loader
GENERATOR = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GENERATOR)


class LeanManifestTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.write_yaml(
            "books.yml",
            manifest_document(
                [
                    book_record(
                        version="0.1.0", label_prefix="sa", lean_module="Sample"
                    ),
                    book_record(
                        "empty",
                        version="0.1.0",
                        label_prefix="em",
                        lean_module="Empty",
                        order=20,
                    ),
                ]
            ),
        )
        for slug in ("sample", "empty"):
            self.write_yaml(
                f"books/{slug}/chapters.yml",
                {
                    "schema_version": 1,
                    "chapters": [
                        {"slug": "first", "title": "First"},
                        {"slug": "second", "title": "Second"},
                    ],
                    "appendices": [{"slug": "background", "title": "Background"}],
                },
            )
            (self.root / "books" / slug / "book.tex").touch()
        self.topic("Chapter01", "VectorSpaces")
        self.topic("Chapter01", "Bases")
        self.manifest("Chapter01", ["VectorSpaces", "Bases"])

    def write_yaml(self, name: str, data: object) -> None:
        write_yaml(self.root / name, data)

    def topic(self, chapter: str, name: str) -> Path:
        path = self.root / "lean/Textbooks/Sample" / chapter / f"{name}.lean"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("-- Mathematical source\n", encoding="utf-8")
        return path

    def manifest(self, chapter: str, modules: object) -> None:
        self.write_yaml(
            f"lean/Textbooks/Sample/{chapter}/modules.yml",
            {"schema_version": 1, "modules": modules},
        )

    def test_reading_order_chapters_appendices_and_empty_book(self) -> None:
        self.topic("Chapter02", "Matrices")
        self.manifest("Chapter02", ["Matrices"])
        self.topic("Appendix01", "Background")
        self.manifest("Appendix01", ["Background"])
        outputs = expected_files(self.root)
        text = outputs[self.root / "lean/Textbooks/Sample/All.lean"]
        imports = [line for line in text.splitlines() if line.startswith("import ")]
        self.assertEqual(
            imports,
            [
                "import Textbooks.Sample.Chapter01.VectorSpaces",
                "import Textbooks.Sample.Chapter01.Bases",
                "import Textbooks.Sample.Chapter02.Matrices",
                "import Textbooks.Sample.Appendix01.Background",
            ],
        )
        self.assertNotIn(
            "import ", outputs[self.root / "lean/Textbooks/Empty/All.lean"]
        )
        self.assertIn(
            "import Textbooks.Empty.All", outputs[self.root / "lean/Textbooks.lean"]
        )

    def test_invalid_module_lists(self) -> None:
        for modules, diagnostic in [
            (["Bases", "Bases"], "duplicate module"),
            (["Missing"], "declared Lean source is missing"),
            (["../Bases"], "invalid topic name"),
            (["01-Bases"], "invalid topic name"),
            (["All"], "invalid topic name"),
            ([None], "invalid topic name"),
            ("Bases", "modules must be a list"),
        ]:
            with self.subTest(modules=modules):
                self.manifest("Chapter01", modules)
                with self.assertRaisesRegex(ValueError, diagnostic):
                    expected_files(self.root)

    def test_missing_manifest(self) -> None:
        (self.root / "lean/Textbooks/Sample/Chapter01/modules.yml").unlink()
        with self.assertRaisesRegex(ValueError, "cannot read YAML"):
            expected_files(self.root)

    def test_unregistered_source(self) -> None:
        self.topic("Chapter01", "Forgotten")
        with self.assertRaisesRegex(ValueError, "Forgotten.lean.*unregistered"):
            expected_files(self.root)

    def test_chapter_outside_contents(self) -> None:
        self.manifest("Chapter03", [])
        with self.assertRaisesRegex(ValueError, "Chapter03/modules.yml.*unregistered"):
            expected_files(self.root)

    def test_unregistered_book(self) -> None:
        self.write_yaml(
            "lean/Textbooks/Unknown/Chapter01/modules.yml",
            {"schema_version": 1, "modules": []},
        )
        with self.assertRaisesRegex(ValueError, "unregistered Lean book"):
            expected_files(self.root)

    def test_schema_validation(self) -> None:
        for data in (
            [],
            {"schema_version": True, "modules": []},
            {"schema_version": 2, "modules": []},
            {"schema_version": 1, "modules": [], "extra": []},
        ):
            with self.subTest(data=data):
                self.write_yaml("lean/Textbooks/Sample/Chapter01/modules.yml", data)
                with self.assertRaises(ValueError):
                    expected_files(self.root)

    def test_check_is_read_only_and_generation_is_idempotent(self) -> None:
        target = self.root / "lean/Textbooks/Sample/All.lean"
        target.write_text("old assembly\n", encoding="utf-8")
        source = self.root / "lean/Textbooks/Sample/Chapter01/Bases.lean"
        original = source.read_bytes()
        with (
            contextlib.redirect_stdout(io.StringIO()),
            contextlib.redirect_stderr(io.StringIO()),
        ):
            self.assertEqual(GENERATOR.generate(root=self.root, check=True), 1)
            self.assertEqual(target.read_text(), "old assembly\n")
            self.assertEqual(GENERATOR.generate(root=self.root), 0)
            timestamp = target.stat().st_mtime_ns
            self.assertEqual(GENERATOR.generate(root=self.root), 0)
            self.assertEqual(target.stat().st_mtime_ns, timestamp)
            self.assertEqual(GENERATOR.generate(root=self.root, check=True), 0)
        self.assertEqual(source.read_bytes(), original)

    def test_selection_preserves_other_book_and_complete_root(self) -> None:
        outputs = expected_files(self.root, "sample")
        self.assertNotIn(self.root / "lean/Textbooks/Empty/All.lean", outputs)
        self.assertIn("Textbooks.Empty.All", outputs[self.root / "lean/Textbooks.lean"])
        with self.assertRaisesRegex(ValueError, "book is not registered"):
            expected_files(self.root, "unknown")


if __name__ == "__main__":
    unittest.main()
