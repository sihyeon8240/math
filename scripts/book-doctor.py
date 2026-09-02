#!/usr/bin/env python3
"""Perform a read-only, best-effort health inspection of one textbook."""

from __future__ import annotations

import sys
from pathlib import Path

try:
    from scripts.book_manifest import load_manifest
    from scripts.contents_manifest import (
        appendix_directory,
        chapter_directory,
        expected_files,
        load_book_contents,
        load_sections,
        section_filenames,
    )
except ModuleNotFoundError:
    from book_manifest import load_manifest
    from contents_manifest import (
        appendix_directory,
        chapter_directory,
        expected_files,
        load_book_contents,
        load_sections,
        section_filenames,
    )

ROOT = Path(__file__).resolve().parent.parent


def read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return ""


def main() -> int:
    slug = sys.argv[1] if len(sys.argv) == 2 else ""
    warnings: list[str] = []

    try:
        manifest = load_manifest()
        record = next(
            (item for item in manifest["books"] if item["slug"] == slug),
            None,
        )

        if not slug:
            warnings.append("usage: python scripts/book-doctor.py <slug>")
        if record is None:
            warnings.append(f"book is not registered: {slug or '(missing slug)'}")

        directory = ROOT / "books" / slug
        entry = read(directory / "book.tex")

        print(f"Book Doctor: {slug or '(none)'}\n" + "=" * 50)

        checks = {
            "Manifest metadata": bool(record),
            "Book structure": bool(entry),
            "Bibliography": (directory / "references.bib").is_file(),
            "Frontmatter fallback": "common/templates" in entry,
        }

        chapters, appendices = load_book_contents(directory)
        assembly_files: list[Path] = []
        section_files: list[Path] = []
        groups = (
            (chapters, chapter_directory),
            (appendices, appendix_directory),
        )
        for entries, directory_for in groups:
            for number, item in enumerate(entries, 1):
                content_dir = directory_for(directory, number, item)
                assembly_files.append(content_dir / "index.tex")
                sections = load_sections(content_dir)
                section_files.extend(
                    content_dir / filename
                    for section_number, section in enumerate(sections, 1)
                    for filename in section_filenames(section_number, section)
                )

        stale = [
            path
            for path, expected in expected_files(directory, book=record).items()
            if read(path) != expected
        ]
        if stale:
            warnings.append(
                "stale generated assembly: "
                + ", ".join(str(path.relative_to(directory)) for path in stale)
            )

        content = "\n".join(read(path) for path in section_files)
        checks.update(
            {
                "Chapter structure": bool(chapters)
                and all(path.is_file() for path in assembly_files)
                and not stale,
                "Section structure": bool(section_files)
                and all(path.is_file() for path in section_files),
                "Labels": "\\label{" in content,
                "References": "\\printbibliography" in entry,
            }
        )
        checks["Repository policy compliance"] = bool(record) and all(checks.values())

        for name, passed in checks.items():
            print(f"{name}: {'OK' if passed else 'CHECK'}")
    except Exception as error:
        warnings.append(f"inspection incomplete: {error}")

    print("\nWarnings")
    print("\n".join(f"- {item}" for item in warnings) or "- None")
    print("\nAdvisory only; no files were modified.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
