#!/usr/bin/env python3
"""Print a best-effort, informational repository overview."""

from __future__ import annotations

from pathlib import Path

try:
    from scripts.bibtex import entry_keys
    from scripts.book_manifest import load_manifest
    from scripts.contents_manifest import (
        appendix_directory,
        chapter_directory,
        load_book_contents,
        load_sections,
        section_filenames,
    )
    from scripts.lean_coverage import book_lean_metrics
except ModuleNotFoundError:
    from bibtex import entry_keys
    from book_manifest import load_manifest
    from contents_manifest import (
        appendix_directory,
        chapter_directory,
        load_book_contents,
        load_sections,
        section_filenames,
    )
    from lean_coverage import book_lean_metrics

ROOT = Path(__file__).resolve().parent.parent
ENVIRONMENTS = {
    "axioms": ("axiom",),
    "theorems": ("theorem", "lemma", "proposition", "corollary"),
    "definitions": ("definition",),
    "examples": ("example",),
    "exercises": ("exercise", "exercises"),
}
REPORT_FIELDS = (
    ("Version", "version"),
    ("Status", "status"),
    ("Chapter count", "chapters"),
    ("Section count", "sections"),
    ("Appendix count", "appendices"),
    ("Bibliography entries", "bibliography"),
    ("Estimated axiom count", "axioms"),
    ("Estimated theorem count", "theorems"),
    ("Lean verified result count", "lean_verified"),
    ("Lean coverage", "lean_coverage"),
    ("Estimated definition count", "definitions"),
    ("Estimated example count", "examples"),
    ("Estimated exercise count", "exercises"),
    ("Estimated source line count", "lines"),
)


def read(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return ""


def count_env(text: str, names: tuple[str, ...]) -> int:
    return sum(text.count(rf"\begin{{{name}}}") for name in names)


def inspect(book: dict) -> dict:
    directory = ROOT / "books" / book["slug"]

    chapter_data, appendix_data = load_book_contents(directory)
    chapter_paths = [
        chapter_directory(directory, number, chapter) / "index.tex"
        for number, chapter in enumerate(chapter_data, 1)
    ]
    appendix_paths = [
        appendix_directory(directory, number, appendix) / "index.tex"
        for number, appendix in enumerate(appendix_data, 1)
    ]
    sections: list[Path] = []
    chapter_sizes: dict[str, int] = {}
    logical_sections = 0

    for chapter in chapter_paths + appendix_paths:
        section_data = load_sections(chapter.parent)
        logical_sections += len(section_data)
        chapter_sections = [
            chapter.parent / filename
            for number, section in enumerate(section_data, 1)
            for filename in section_filenames(number, section)
        ]

        sections.extend(chapter_sections)
        chapter_sizes[chapter.parent.name] = sum(
            len(read(path).splitlines()) for path in chapter_sections
        )

    content = "\n".join(read(path) for path in sections)
    lines = len(content.splitlines())
    bibliography = len(entry_keys(read(directory / "references.bib")))
    largest_section = max(
        (
            (
                path.relative_to(directory).as_posix(),
                len(read(path).splitlines()),
            )
            for path in sections
        ),
        key=lambda item: item[1],
        default=("none", 0),
    )

    lean = book_lean_metrics(book["slug"])
    result = {
        "title": book.get("title", book["slug"]),
        "version": book["version"],
        "status": book.get("status", "unknown"),
        "chapters": len(chapter_paths),
        "sections": logical_sections,
        "appendices": len(appendix_paths),
        "bibliography": bibliography,
        "lines": lines,
        "lean_verified": lean["verified"],
        "lean_coverage": (
            f"{lean['percentage']:.1f}% ({lean['verified']}/{lean['total']} results)"
        ),
        "largest_chapter": (
            max(chapter_sizes.items(), key=lambda item: item[1])
            if chapter_sizes
            else ("none", 0)
        ),
        "largest_section": largest_section,
    }
    result.update(
        {
            name: count_env(content, environments)
            for name, environments in ENVIRONMENTS.items()
        }
    )
    return result


def main() -> int:
    try:
        books = load_manifest()["books"]
        data = [inspect(book) for book in books]

        print(
            "=" * 50
            + "\nUNDERGRADUATE MATHEMATICS TEXTBOOK REPOSITORY"
            + "\nRepository Report\n"
            + "=" * 50
        )
        print(
            f"\nRepository\n\n"
            f"Books: {len(books)}\n"
            f"Buildable: {sum(bool(item.get('build')) for item in books)}\n"
            f"Release enabled: {sum(bool(item.get('release')) for item in books)}\n"
            "Published on site: "
            f"{sum(bool(item.get('site')) for item in books)}"
        )

        for item in data:
            print("\n" + "-" * 50 + f"\n\n{item['title']}")
            for label, key in REPORT_FIELDS:
                print(f"{label}: {item[key]}")

        chapters = sum(item["chapters"] for item in data)
        sections = sum(item["sections"] for item in data)
        lines = sum(item["lines"] for item in data)
        largest_chapter = max(
            ((item["title"], *item["largest_chapter"]) for item in data),
            key=lambda item: item[2],
            default=("none", "none", 0),
        )
        largest_section = max(
            ((item["title"], *item["largest_section"]) for item in data),
            key=lambda item: item[2],
            default=("none", "none", 0),
        )

        print("\n" + "=" * 50 + "\nRepository Totals\n" + "=" * 50)
        if chapters:
            print(
                f"Chapters: {chapters}\n"
                f"Sections: {sections}\n"
                "Appendices: "
                f"{sum(item['appendices'] for item in data)}\n"
                "Bibliography entries: "
                f"{sum(item['bibliography'] for item in data)}\n"
                f"Source lines: {lines}\n"
                "Average sections per chapter: "
                f"{sections / chapters:.2f}"
            )
        else:
            print("No chapters found")

        print(
            "Largest chapter: "
            f"{largest_chapter[0]} / {largest_chapter[1]} "
            f"({largest_chapter[2]} lines)\n"
            "Largest section: "
            f"{largest_section[0]} / {largest_section[1]} "
            f"({largest_section[2]} lines)\n"
            "Draft books: "
            f"{sum(item['status'] == 'draft' for item in data)}\n"
            "Books in review: "
            f"{sum(item['status'] == 'review' for item in data)}\n"
            "Published books: "
            f"{sum(item['status'] == 'published' for item in data)}\n"
            "Archived books: "
            f"{sum(item['status'] == 'archived' for item in data)}"
        )
        print(
            "\nMetrics are lightweight source estimates. "
            "This command never modifies files."
        )
    except Exception as error:
        print(f"warning: report is incomplete: {error}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
