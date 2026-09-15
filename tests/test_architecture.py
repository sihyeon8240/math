"""Regression tests for architecture policy validation."""

from __future__ import annotations

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "check_architecture", ROOT / "scripts/check-architecture.py"
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


class ArchitectureTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.book = self.root / "books/sample"
        chapter = self.book / "chapters/01-start"
        front = self.book / "frontmatter"
        chapter.mkdir(parents=True)
        front.mkdir()
        (self.root / "docs").mkdir()
        (self.root / "docs" / "ARCHITECTURE.md").write_text(
            "contract\n", encoding="utf-8"
        )
        self.write_manifest()
        self.entry(
            r"\addbibresource{references.bib}"
            "\n"
            r"\include{frontmatter/title-and-copyright}"
            "\n"
            r"\include{frontmatter/preface}"
            "\n"
            r"\include{chapters/01-start/index}"
            "\n"
            r"\nocite{*}"
            "\n"
        )
        (chapter / "index.tex").write_text(
            r"\chapter{Start}" "\n" r"\input{01-section}" "\n",
            encoding="utf-8",
        )
        (chapter / "01-section.tex").write_text(r"\section{One}" "\n", encoding="utf-8")
        (self.book / "chapters.yml").write_text(
            "schema_version: 1\nchapters:\n  - slug: start\n    title: Start\n",
            encoding="utf-8",
        )
        (chapter / "sections.yml").write_text(
            "schema_version: 1\nsections:\n  - slug: section\n    title: One\n",
            encoding="utf-8",
        )
        (self.book / "references.bib").write_text(
            "@book{one, title={One}}\n", encoding="utf-8"
        )
        (front / "title-and-copyright.tex").write_text(
            r"\input{title-and-copyright}" "\n",
            encoding="utf-8",
        )
        (front / "preface.tex").write_text(
            r"\input{preface}" "\n",
            encoding="utf-8",
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def write_manifest(self, **book_overrides: object) -> None:
        book = {
            "slug": "sample",
            "title": "Sample",
            "version": "1.0.0",
            "status": "draft",
            "order": 10,
        }
        book.update(book_overrides)
        manifest = {
            "schema_version": 1,
            "defaults": {
                "author": "Sample Author",
                "build": True,
                "check": True,
                "release": False,
                "site": False,
            },
            "books": [book],
        }
        (self.root / "books.yml").write_text(
            yaml.safe_dump(manifest, sort_keys=False), encoding="utf-8"
        )

    def entry(self, text: str) -> None:
        (self.book / "book.tex").write_text(text, encoding="utf-8")

    def findings(self):
        return MODULE.validate_repository(self.root)

    def assert_error(self, fragment: str) -> None:
        errors = self.findings().errors
        self.assertTrue(any(fragment in error for error in errors), "\n".join(errors))

    def add_chapter(self, name: str, title: str = "Next") -> None:
        chapter = self.book / "chapters" / name
        chapter.mkdir()
        (chapter / "index.tex").write_text(
            rf"\chapter{{{title}}}" + "\n" + r"\input{01-placeholder}" + "\n",
            encoding="utf-8",
        )
        (chapter / "01-placeholder.tex").write_text("body\n", encoding="utf-8")
        manifest_path = self.book / "chapters.yml"
        manifest = yaml.safe_load(manifest_path.read_text(encoding="utf-8"))
        manifest["chapters"].append({"slug": name.split("-", 1)[1], "title": title})
        manifest_path.write_text(
            yaml.safe_dump(manifest, sort_keys=False), encoding="utf-8"
        )
        (chapter / "sections.yml").write_text(
            "schema_version: 1\nsections:\n  - slug: placeholder\n    title: Placeholder\n",
            encoding="utf-8",
        )

    def rename_first_chapter(self, name: str) -> None:
        old = self.book / "chapters/01-start"
        old.rename(self.book / "chapters" / name)
        entry = (self.book / "book.tex").read_text(encoding="utf-8")
        self.entry(entry.replace("chapters/01-start", f"chapters/{name}"))

    def restore_first_chapter(self, name: str) -> None:
        current = self.book / "chapters" / name
        current.rename(self.book / "chapters/01-start")
        entry = (self.book / "book.tex").read_text(encoding="utf-8")
        self.entry(entry.replace(f"chapters/{name}", "chapters/01-start"))

    def test_current_repository_complies(self) -> None:
        findings = MODULE.validate_repository(ROOT)
        self.assertEqual(findings.errors, [], "\n".join(findings.errors))

    def test_minimal_fixture_complies(self) -> None:
        self.assertEqual(self.findings().errors, [])

    def test_two_consecutive_chapters_comply(self) -> None:
        self.add_chapter("02-next")
        entry = (self.book / "book.tex").read_text(encoding="utf-8")
        self.entry(entry + r"\include{chapters/02-next/index}" + "\n")
        self.assertEqual(self.findings().errors, [])

    def test_one_digit_chapter_number_is_error(self) -> None:
        self.rename_first_chapter("1-start")
        self.assert_error("chapter directory name must match")

    def test_three_digit_chapter_number_is_error(self) -> None:
        self.rename_first_chapter("001-start")
        self.assert_error("chapter directory name must match")

    def test_invalid_chapter_name_characters_are_errors(self) -> None:
        for name in ("01-Start", "01-vector_spaces", "01-vector--spaces"):
            with self.subTest(name=name):
                self.rename_first_chapter(name)
                self.assert_error("chapter directory name must match")
                self.restore_first_chapter(name)

    def test_skipped_chapter_number_is_error(self) -> None:
        self.add_chapter("03-third")
        self.assert_error("chapter numbers are 01, 03; expected 01, 02")

    def test_first_chapter_number_must_be_one(self) -> None:
        self.rename_first_chapter("02-start")
        self.assert_error("chapter numbers are 02; expected 01")

    def test_duplicate_chapter_number_is_error(self) -> None:
        self.add_chapter("01-again", "Again")
        self.assert_error("duplicate chapter number 01")

    def test_reversed_chapter_include_order_is_error(self) -> None:
        self.add_chapter("02-next")
        self.entry(
            r"\addbibresource{references.bib}"
            "\n"
            r"\include{chapters/02-next/index}"
            "\n"
            r"\include{chapters/01-start/index}"
            "\n"
            r"\nocite{*}"
            "\n"
        )
        self.assert_error("chapter include order is 02, 01; expected 01, 02")

    def test_manifest_validation_error_is_reported(self) -> None:
        self.write_manifest(unexpected_field="value")
        self.assert_error("unknown field(s): unexpected_field")

    def test_orphan_section_is_error(self) -> None:
        (self.book / "chapters/01-start/02-orphan.tex").write_text("", encoding="utf-8")
        self.assert_error("orphan section file")

    def test_orphan_chapter_directory_is_error(self) -> None:
        self.add_chapter("02-orphan", "Orphan")
        self.assert_error("orphan chapter directory")

    def test_chapter_target_must_be_index(self) -> None:
        self.entry(
            r"\addbibresource{references.bib}"
            "\n"
            r"\include{chapters/01-start/01-section}"
            "\n"
        )
        self.assert_error("chapter target is not index.tex")

    def test_chapter_requires_exactly_one_declaration(self) -> None:
        (self.book / "chapters/01-start/index.tex").write_text(
            r"\chapter{One}"
            "\n"
            r"\chapter{Two}"
            "\n"
            r"\input{01-section}"
            "\n",
            encoding="utf-8",
        )
        self.assert_error("expected one chapter declaration")

    def test_missing_required_bibliography_is_error(self) -> None:
        (self.book / "references.bib").unlink()
        self.assert_error("required bibliography is missing")

    def test_missing_configured_bibliography_is_error(self) -> None:
        self.entry(
            r"\addbibresource{missing.bib}"
            "\n"
            r"\include{chapters/01-start/index}"
            "\n"
        )
        self.assert_error("configured bibliography does not exist")

    def test_duplicate_bibliography_key_is_error(self) -> None:
        (self.book / "second.bib").write_text(
            "@book{one, title={Again}}\n", encoding="utf-8"
        )
        self.entry(
            r"\addbibresource{references.bib}"
            "\n"
            r"\addbibresource{second.bib}"
            "\n"
            r"\include{chapters/01-start/index}"
            "\n"
        )
        self.assert_error("duplicate bibliography key 'one'")

    def test_duplicate_include_and_input_target_is_error(self) -> None:
        (self.book / "chapters/01-start/index.tex").write_text(
            r"\chapter{Start}"
            "\n"
            r"\input{01-section}"
            "\n"
            r"\include{01-section}"
            "\n",
            encoding="utf-8",
        )
        self.assert_error("duplicate include/input target")

    def set_sections(
        self, filenames: list[str], inputs: list[str] | None = None
    ) -> None:
        chapter = self.book / "chapters/01-start"
        for path in chapter.glob("*.tex"):
            if path.name != "index.tex":
                path.unlink()
        for filename in filenames:
            (chapter / filename).write_text("body\n", encoding="utf-8")
        targets = inputs if inputs is not None else filenames
        lines = [r"\chapter{Start}"] + [rf"\input{{{target}}}" for target in targets]
        (chapter / "index.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")
        findings = MODULE.Findings()
        parsed = MODULE.parse_section_sources(
            [chapter / filename for filename in filenames], chapter.name, findings
        )
        if not findings.errors:
            grouped: dict[tuple[int, str], list[object]] = {}
            for source in parsed:
                grouped.setdefault((source.number, source.slug), []).append(source)
            sections = []
            for (_, slug), sources in sorted(grouped.items()):
                item = {"slug": slug, "title": slug.replace("-", " ").title()}
                sections.append(item)
            (chapter / "sections.yml").write_text(
                yaml.safe_dump(
                    {"schema_version": 1, "sections": sections}, sort_keys=False
                ),
                encoding="utf-8",
            )

    def test_generated_appendix_paths_pass_architecture_checks(self) -> None:
        appendix = self.book / "appendices/01-tables"
        appendix.mkdir(parents=True)
        manifest = self.book / "chapters.yml"
        manifest.write_text(
            manifest.read_text() + "appendices:\n  - slug: tables\n    title: Tables\n"
        )
        (appendix / "sections.yml").write_text(
            "schema_version: 1\nsections:\n  - slug: values\n    title: Values\n"
        )
        source = appendix / "01-values.tex"
        source.write_text("Body.\n")
        entry = self.book / "book.tex"
        entry.write_text(
            entry.read_text() + "\\appendix\n\\include{appendices/01-tables/index}\n"
        )
        (appendix / "index.tex").write_text(
            "\\chapter{Tables}\n\\section{Values}\n"
            "\\input{appendices/01-tables/01-values.tex}\n"
        )
        self.assertEqual(self.findings().errors, [])
        source.unlink()
        self.assert_error("target does not exist")

    def test_consecutive_single_sections_comply(self) -> None:
        self.set_sections(["01-introduction.tex", "02-main-result.tex"])
        self.assertEqual(self.findings().errors, [])

    def test_mixed_input_extensions_comply(self) -> None:
        self.set_sections(
            ["01-first.tex", "02-second.tex"], ["01-first", "02-second.tex"]
        )
        self.assertEqual(self.findings().errors, [])

    def test_multiple_sources_per_section_are_rejected(self) -> None:
        for files in (
            ["01-topic-a.tex", "01-topic-b.tex"],
            ["01-topic.tex", "01-topic-b.tex"],
            ["01-first.tex", "01-second.tex"],
        ):
            with self.subTest(files=files):
                self.set_sections(files)
                self.assert_error("must have exactly one source file")

    def test_logical_section_number_gap_is_error(self) -> None:
        self.set_sections(["01-first.tex", "03-third.tex"])
        self.assert_error("logical section numbers are 01, 03; expected 01, 02")

    def test_logical_sections_must_be_in_numeric_order(self) -> None:
        self.set_sections(["01-first.tex", "02-second.tex"], ["02-second", "01-first"])
        self.assert_error("must follow logical section number order")

    def test_missing_orphan_and_duplicate_inputs_are_errors(self) -> None:
        cases = [
            (
                ["01-topic.tex", "02-other.tex"],
                ["01-topic"],
                "orphan section file",
            ),
            (
                ["01-topic.tex", "02-other.tex"],
                ["01-topic", "02-other", "01-missing-c"],
                "target does not exist",
            ),
            (
                ["01-topic.tex", "02-other.tex"],
                ["01-topic", "01-topic", "02-other"],
                "duplicate include/input target",
            ),
        ]
        for files, inputs, diagnostic in cases:
            with self.subTest(diagnostic=diagnostic):
                self.set_sections(files, inputs)
                self.assert_error(diagnostic)

    def test_invalid_section_filename_forms_are_errors(self) -> None:
        invalid_names = (
            "01-topic-A.tex",
            "01-topic--name.tex",
            "1-topic.tex",
            "01-section-part-2.tex",
        )
        for filename in invalid_names:
            with self.subTest(filename=filename):
                self.set_sections([filename])
                self.assertTrue(self.findings().errors)


if __name__ == "__main__":
    unittest.main()
