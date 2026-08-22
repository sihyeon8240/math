#!/usr/bin/env python3
"""Generate the root book table and each book README detail section."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from book_manifest import load_manifest
from latex_titles import braced_argument, chapter_titles, plain_text_title

REPO_ROOT = Path(__file__).resolve().parent.parent
README_PATH = REPO_ROOT / "README.md"
BOOKS_DIR = REPO_ROOT / "books"
BEGIN_MARKER = "<!-- BEGIN GENERATED BOOKS -->"
END_MARKER = "<!-- END GENERATED BOOKS -->"
DETAILS_BEGIN_MARKER = "<!-- BEGIN GENERATED BOOK DETAILS -->"
DETAILS_END_MARKER = "<!-- END GENERATED BOOK DETAILS -->"
INCLUDE = re.compile(r"\\(?:include|input)\s*\{([^}]+)\}")
BIB_ENTRY = re.compile(r"@(?P<type>[A-Za-z]+)\s*")
BIB_FIELD = re.compile(r"(?:^|,)\s*(?P<name>[A-Za-z]+)\s*=\s*", re.MULTILINE)


def _escape_table_cell(value: str) -> str:
    return value.replace("\\", "\\\\").replace("|", "\\|")


def render_books_table(manifest: dict) -> str:
    lines = ["| Book | Slug | Build command |", "|---|---|---|"]
    for book in manifest["books"]:
        slug = book["slug"]
        lines.append(
            f"| {_escape_table_cell(book['title'])} | `{slug}` | "
            f"`make books BOOK={slug}` |"
        )
    return "\n".join(lines)


def replace_generated_books(readme: str, table: str) -> str:
    begin_count = readme.count(BEGIN_MARKER)
    end_count = readme.count(END_MARKER)
    if begin_count != 1:
        raise ValueError(
            f"README must contain exactly one {BEGIN_MARKER!r} marker; found {begin_count}"
        )
    if end_count != 1:
        raise ValueError(
            f"README must contain exactly one {END_MARKER!r} marker; found {end_count}"
        )
    begin = readme.index(BEGIN_MARKER) + len(BEGIN_MARKER)
    end = readme.index(END_MARKER)
    if begin > end:
        raise ValueError("README generated books markers are in the wrong order")
    return readme[:begin] + "\n\n" + table + "\n\n" + readme[end:]


def assembly_titles(book_dir: Path) -> tuple[list[str], list[str]]:
    entry = (book_dir / "book.tex").read_text(encoding="utf-8")
    chapters: list[str] = []
    appendices: list[str] = []
    for target in INCLUDE.findall(entry):
        if target.startswith("chapters/"):
            destination = chapters
        elif target.startswith("appendices/"):
            destination = appendices
        else:
            continue
        path = book_dir / target
        if path.suffix != ".tex":
            path = path.with_suffix(".tex")
        matches = chapter_titles(path.read_text(encoding="utf-8"))
        if len(matches) != 1:
            raise ValueError(f"{path} must contain exactly one chapter title")
        destination.append(plain_text_title(matches[0]))
    if not chapters:
        raise ValueError(f"{book_dir / 'book.tex'} does not include any chapters")
    return chapters, appendices


def bibliography_entries(path: Path) -> list[dict[str, str]]:
    text = path.read_text(encoding="utf-8")
    entries: list[dict[str, str]] = []
    for match in BIB_ENTRY.finditer(text):
        body, _ = braced_argument(text, match.end())
        fields: dict[str, str] = {}
        for field in BIB_FIELD.finditer(body):
            value, _ = braced_argument(body, field.end())
            fields[field.group("name").lower()] = value.strip()
        fields["entrytype"] = match.group("type").lower()
        missing = {"title"} - fields.keys()
        if missing:
            raise ValueError(
                f"{path} reference is missing: {', '.join(sorted(missing))}"
            )
        entries.append(fields)
    return entries


def display_authors(value: str) -> str:
    authors: list[str] = []
    for author in value.split(" and "):
        family, separator, given = author.partition(",")
        authors.append(
            f"{given.strip()} {family.strip()}" if separator else author.strip()
        )
    return ", ".join(authors)


def render_reference(reference: dict[str, str]) -> str:
    parts: list[str] = []
    if author := reference.get("author"):
        parts.append(display_authors(author))
    parts.append(f"*{reference['title']}*")
    for field in (
        "publisher",
        "journaltitle",
        "booktitle",
        "institution",
        "organization",
    ):
        if value := reference.get(field):
            parts.append(value)
            break
    if year := reference.get("year"):
        parts.append(year)
    return ", ".join(parts) + "."


def render_book_details(book_dir: Path, slug: str) -> str:
    chapters, appendices = assembly_titles(book_dir)
    lines = [
        "## Chapters",
        "",
        *(f"{number}. {title}" for number, title in enumerate(chapters, 1)),
    ]
    if appendices:
        lines.extend(("", *appendices))

    references = bibliography_entries(book_dir / "references.bib")
    if references:
        heading = "## Main reference" if len(references) == 1 else "## Main references"
        lines.extend(("", heading, ""))
        for reference in references:
            citation = render_reference(reference)
            lines.append(citation if len(references) == 1 else f"- {citation}")

    lines.extend(
        (
            "",
            "## Build and feedback",
            "",
            f"    make books BOOK={slug}",
            "",
            "Report errors through a GitHub Issue with the chapter, section, and relevant "
            "source location. See docs/CONTRIBUTING.md before submitting a pull request.",
        )
    )
    return "\n".join(lines)


def replace_generated_details(readme: str, details: str, path: Path) -> str:
    begin_count = readme.count(DETAILS_BEGIN_MARKER)
    end_count = readme.count(DETAILS_END_MARKER)
    if begin_count != 1 or end_count != 1:
        raise ValueError(
            f"{path} must contain exactly one {DETAILS_BEGIN_MARKER!r} and "
            f"{DETAILS_END_MARKER!r} marker"
        )
    begin = readme.index(DETAILS_BEGIN_MARKER) + len(DETAILS_BEGIN_MARKER)
    end = readme.index(DETAILS_END_MARKER)
    if begin > end:
        raise ValueError(f"{path} generated chapter markers are in the wrong order")
    return readme[:begin] + "\n\n" + details + "\n\n" + readme[end:]


def generate(
    *,
    check: bool = False,
    readme_path: Path = README_PATH,
    manifest: dict | None = None,
    books_dir: Path = BOOKS_DIR,
    scope: str = "all",
    book: str | None = None,
) -> int:
    manifest = load_manifest() if manifest is None else manifest
    if scope not in {"all", "root", "books"}:
        raise ValueError(f"unknown README generation scope: {scope}")
    if book and scope != "books":
        raise ValueError("--book requires --books")
    selected_books = manifest["books"]
    if book:
        selected_books = [item for item in selected_books if item["slug"] == book]
        if not selected_books:
            raise ValueError(f"book is not registered in books.yml: {book}")

    root_update: tuple[str, str] | None = None
    stale = False
    if scope in {"all", "root"}:
        current = readme_path.read_bytes().decode("utf-8")
        expected = replace_generated_books(current, render_books_table(manifest))
        root_update = (current, expected)
        stale = current != expected

    book_updates: list[tuple[Path, str, str]] = []
    if scope in {"all", "books"}:
        for item in selected_books:
            path = books_dir / item["slug"] / "README.md"
            book_current = path.read_text(encoding="utf-8")
            book_expected = replace_generated_details(
                book_current, render_book_details(path.parent, item["slug"]), path
            )
            book_updates.append((path, book_current, book_expected))
            stale = stale or book_current != book_expected
    if check:
        if stale:
            print("error: generated README content is stale", file=sys.stderr)
            return 1
        print("Generated README content is up to date.")
        return 0
    if root_update:
        readme_path.write_bytes(root_update[1].encode("utf-8"))
    for path, _, book_expected in book_updates:
        path.write_text(book_expected, encoding="utf-8")
    parts = []
    if root_update:
        display = (
            readme_path.relative_to(REPO_ROOT)
            if readme_path.is_relative_to(REPO_ROOT)
            else readme_path
        )
        parts.append(f"book table in {display}")
    if book_updates:
        parts.append(f"{len(book_updates)} book detail section(s)")
    print("Generated " + " and ".join(parts))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true", help="fail instead of updating stale output"
    )
    scope = parser.add_mutually_exclusive_group()
    scope.add_argument("--root", action="store_const", const="root", dest="scope")
    scope.add_argument("--books", action="store_const", const="books", dest="scope")
    parser.set_defaults(scope="all")
    parser.add_argument(
        "--book", metavar="SLUG", help="limit --books to one registered book"
    )
    args = parser.parse_args()
    try:
        return generate(check=args.check, scope=args.scope, book=args.book)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
