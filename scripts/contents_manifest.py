"""Load and render the declarative textbook contents manifests."""

from __future__ import annotations

import re
from pathlib import Path

import yaml

try:
    from scripts.latex_scan import command_arguments, has_balanced_braces
except ModuleNotFoundError:
    from latex_scan import command_arguments, has_balanced_braces

SCHEMA_VERSION = 1
SLUG = re.compile(r"^[a-z0-9]+(?:-[a-z0-9]+)*$")
BEGIN_CHAPTERS = "% BEGIN GENERATED CHAPTERS"
END_CHAPTERS = "% END GENERATED CHAPTERS"
BEGIN_APPENDICES = "% BEGIN GENERATED APPENDICES"
END_APPENDICES = "% END GENERATED APPENDICES"
BEGIN_METADATA = "% BEGIN GENERATED METADATA"
END_METADATA = "% END GENERATED METADATA"
GENERATED_NOTICE = "% Generated from contents manifests; do not edit."


def _mapping(path: Path) -> dict:
    try:
        value = yaml.safe_load(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, yaml.YAMLError) as error:
        raise ValueError(f"{path}: cannot read YAML: {error}") from error
    if not isinstance(value, dict):
        raise ValueError(f"{path}: root must be a mapping")
    if value.get("schema_version") != SCHEMA_VERSION:
        raise ValueError(f"{path}: schema_version must be {SCHEMA_VERSION}")
    return value


def _entries(path: Path, field: str, allowed: set[str]) -> list[dict]:
    data = _mapping(path)
    unknown_root = set(data) - {"schema_version", field}
    if unknown_root:
        raise ValueError(f"{path}: unknown field(s): {', '.join(sorted(unknown_root))}")
    values = data.get(field)
    if not isinstance(values, list) or not values:
        raise ValueError(f"{path}: {field} must be a non-empty list")
    seen: set[str] = set()
    for number, item in enumerate(values, 1):
        prefix = f"{path}: {field}[{number}]"
        if not isinstance(item, dict):
            raise ValueError(f"{prefix} must be a mapping")
        unknown = set(item) - allowed
        if unknown:
            raise ValueError(
                f"{prefix}: unknown field(s): {', '.join(sorted(unknown))}"
            )
        slug = item.get("slug")
        title = item.get("title")
        if not isinstance(slug, str) or not SLUG.fullmatch(slug):
            raise ValueError(f"{prefix}.slug must be lowercase hyphenated text")
        if slug in seen:
            raise ValueError(f"{path}: duplicate {field[:-1]} slug {slug!r}")
        seen.add(slug)
        if (
            not isinstance(title, str)
            or not title.strip()
            or "\n" in title
            or "\r" in title
            or not has_balanced_braces(title)
        ):
            raise ValueError(
                f"{prefix}.title must be a non-empty, balanced single-line string"
            )
    return values


def load_book_contents(book_dir: Path) -> tuple[list[dict], list[dict]]:
    path = book_dir / "chapters.yml"
    data = _mapping(path)
    unknown_root = set(data) - {"schema_version", "chapters", "appendices"}
    if unknown_root:
        raise ValueError(
            f"{path}: unknown field(s): " + ", ".join(sorted(unknown_root))
        )

    chapters = data.get("chapters")
    appendices = data.get("appendices", [])
    for field, values, required in (
        ("chapters", chapters, True),
        ("appendices", appendices, False),
    ):
        if not isinstance(values, list) or (required and not values):
            raise ValueError(f"{path}: {field} must be a non-empty list")
        if not required and "appendices" in data and not values:
            raise ValueError(
                f"{path}: appendices must be a non-empty list when present"
            )
        seen: set[str] = set()
        for number, item in enumerate(values, 1):
            prefix = f"{path}: {field}[{number}]"
            if not isinstance(item, dict):
                raise ValueError(f"{prefix} must be a mapping")
            unknown = set(item) - {"slug", "title"}
            if unknown:
                raise ValueError(
                    f"{prefix}: unknown field(s): {', '.join(sorted(unknown))}"
                )
            slug, title = item.get("slug"), item.get("title")
            if not isinstance(slug, str) or not SLUG.fullmatch(slug):
                raise ValueError(f"{prefix}.slug must be lowercase hyphenated text")
            if slug in seen:
                raise ValueError(f"{path}: duplicate {field[:-1]} slug {slug!r}")
            seen.add(slug)
            if (
                not isinstance(title, str)
                or not title.strip()
                or "\n" in title
                or "\r" in title
                or not has_balanced_braces(title)
            ):
                raise ValueError(
                    f"{prefix}.title must be a non-empty, balanced single-line string"
                )
    return chapters, appendices


def load_chapters(book_dir: Path) -> list[dict]:
    return load_book_contents(book_dir)[0]


def load_sections(chapter_dir: Path) -> list[dict]:
    path = chapter_dir / "sections.yml"
    sections = _entries(path, "sections", {"slug", "title", "split"})
    for number, section in enumerate(sections, 1):
        split = section.get("split")
        if split is None:
            continue
        if type(split) is not int or not 2 <= split <= 26:
            raise ValueError(
                f"{path}: sections[{number}].split must be an integer from 2 to 26"
            )
    return sections


def chapter_directory(book_dir: Path, number: int, chapter: dict) -> Path:
    return book_dir / "chapters" / f"{number:02d}-{chapter['slug']}"


def appendix_directory(book_dir: Path, number: int, appendix: dict) -> Path:
    return book_dir / "appendices" / f"{number:02d}-{appendix['slug']}"


def section_filenames(number: int, section: dict) -> list[str]:
    base = f"{number:02d}-{section['slug']}"
    split = section.get("split")
    if split is None:
        return [f"{base}.tex"]
    return [f"{base}-{chr(ord('a') + offset)}.tex" for offset in range(split)]


def render_include_block(entries: list[dict], kind: str) -> str:
    begin, end = (
        (BEGIN_CHAPTERS, END_CHAPTERS)
        if kind == "chapters"
        else (BEGIN_APPENDICES, END_APPENDICES)
    )
    lines = [begin]
    lines.extend(
        f"\\include{{{kind}/{number:02d}-{entry['slug']}/index}}"
        for number, entry in enumerate(entries, 1)
    )
    lines.append(end)
    return "\n".join(lines)


def render_metadata(book: dict) -> str:
    return "\n".join(
        (
            BEGIN_METADATA,
            f"\\newcommand{{\\name}}{{{book['author']}}}",
            f"\\newcommand{{\\displaytitle}}{{{book['title']}}}",
            f"\\newcommand{{\\version}}{{{book['version']}}}",
            f"\\newcommand{{\\slug}}{{{book['slug']}}}",
            r"\title{\displaytitle}",
            r"\author{\name}",
            r"\hypersetup{pdftitle={\displaytitle},pdfauthor={\name}}",
            END_METADATA,
        )
    )


def replace_generated_block(
    text: str, rendered: str, path: Path, begin: str, end: str
) -> str:
    if text.count(begin) != 1 or text.count(end) != 1:
        raise ValueError(f"{path}: expected exactly one {begin!r} and {end!r}")
    start = text.index(begin)
    finish = text.index(end, start) + len(end)
    return text[:start] + rendered + text[finish:]


def render_contents_index(book_dir: Path, directory: Path, entry: dict) -> str:
    sections = load_sections(directory)
    lines = [GENERATED_NOTICE, "", f"\\chapter{{{entry['title']}}}"]
    relative = directory.relative_to(book_dir).as_posix()
    for section_number, section in enumerate(sections, 1):
        lines.extend(("", f"\\section{{{section['title']}}}"))
        lines.extend(
            f"\\input{{{relative}/{filename}}}"
            for filename in section_filenames(section_number, section)
        )
    return "\n".join(lines) + "\n"


def expected_files(
    book_dir: Path, scope: str = "all", book: dict | None = None
) -> dict[Path, str]:
    chapters, appendices = load_book_contents(book_dir)
    expected: dict[Path, str] = {}
    if scope in {"chap", "all"}:
        path = book_dir / "book.tex"
        if book is None:
            raise ValueError(f"{path}: book manifest record is required")
        template_path = (
            Path(__file__).resolve().parent.parent / "common/templates/book.tex"
        )
        original = template_path.read_text(encoding="utf-8")
        original = replace_generated_block(
            original,
            render_metadata(book),
            template_path,
            BEGIN_METADATA,
            END_METADATA,
        )
        if original.count(r"\backmatter") != 1 or original.index(
            BEGIN_APPENDICES
        ) < original.index(r"\backmatter"):
            raise ValueError(
                f"{template_path}: generated appendices block must follow exactly one \\backmatter"
            )
        text = replace_generated_block(
            original,
            render_include_block(chapters, "chapters"),
            template_path,
            BEGIN_CHAPTERS,
            END_CHAPTERS,
        )
        expected[path] = replace_generated_block(
            text,
            render_include_block(appendices, "appendices"),
            template_path,
            BEGIN_APPENDICES,
            END_APPENDICES,
        )
    if scope in {"sec", "all"}:
        groups = ((chapters, chapter_directory), (appendices, appendix_directory))
        for entries, directory_for in groups:
            for number, entry in enumerate(entries, 1):
                directory = directory_for(book_dir, number, entry)
                expected[directory / "index.tex"] = render_contents_index(
                    book_dir, directory, entry
                )
                sections = load_sections(directory)
                expected_sources = {
                    directory / filename
                    for section_number, section in enumerate(sections, 1)
                    for filename in section_filenames(section_number, section)
                }
                actual_sources = {
                    path for path in directory.glob("*.tex") if path.name != "index.tex"
                }
                missing = sorted(expected_sources - actual_sources)
                orphaned = sorted(actual_sources - expected_sources)
                if missing:
                    raise ValueError(
                        f"{missing[0]}: declared section source is missing"
                    )
                if orphaned:
                    raise ValueError(f"{orphaned[0]}: orphan section source")
                for source in sorted(expected_sources):
                    if command_arguments(
                        source.read_text(encoding="utf-8"), {"section"}
                    ):
                        raise ValueError(
                            f"{source}: section declarations belong in sections.yml"
                        )
    return expected
