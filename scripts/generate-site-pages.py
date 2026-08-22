#!/usr/bin/env python3
"""Generate deterministic Jekyll book pages from the canonical manifest."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import yaml

try:
    from scripts.book_manifest import STATUS_LABELS, load_manifest
    from scripts.lean_coverage import book_lean_metrics
except ModuleNotFoundError:
    from book_manifest import STATUS_LABELS, load_manifest
    from lean_coverage import book_lean_metrics

REPO_ROOT = Path(__file__).resolve().parent.parent
PAGES_DIR = REPO_ROOT / "site" / "books"
SITE_FIELDS = ("slug", "title", "short_title", "status", "order", "site")


def site_books(manifest: dict) -> list[dict]:
    books = []
    for source in manifest["books"]:
        if not source["site"]:
            continue
        book = {field: source.get(field) for field in SITE_FIELDS}
        book["display_short_title"] = source.get("short_title") or source["title"]
        book["status_label"] = STATUS_LABELS[source["status"]]
        lean = book_lean_metrics(source["slug"])
        book["lean_verified"] = lean["verified"]
        book["lean_total"] = lean["total"]
        book["lean_coverage"] = lean["percentage"]
        books.append(book)
    return books


def render_site_page(book: dict) -> str:
    """Render manifest-derived metadata as a book page's front matter."""
    front_matter = {"layout": "book", **book}
    return (
        "---\n"
        + yaml.safe_dump(front_matter, allow_unicode=True, sort_keys=False)
        + "---\n"
    )


def render_site_pages(manifest: dict) -> dict[str, str]:
    return {
        f"{book['slug']}.md": render_site_page(book) for book in site_books(manifest)
    }


def generate(
    *,
    check: bool = False,
    pages_dir: Path = PAGES_DIR,
    book: str | None = None,
) -> int:
    manifest = load_manifest()
    if book:
        registered = {item["slug"]: item for item in manifest["books"]}
        if book not in registered:
            raise ValueError(f"book is not registered in books.yml: {book}")
        if not registered[book]["site"]:
            raise ValueError(f"book is not enabled for site in books.yml: {book}")
    books = site_books(manifest)
    books_by_slug = {item["slug"]: item for item in books}
    expected_names = {f"{item['slug']}.md" for item in books}
    selected_pages = (
        {f"{book}.md": render_site_page(books_by_slug[book])}
        if book
        else render_site_pages(manifest)
    )
    if check:
        print(f"Validated {len(selected_pages)} generated site book page(s)")
        return 0
    pages_dir.mkdir(parents=True, exist_ok=True)
    if not book:
        for path in pages_dir.glob("*.md"):
            if path.name not in expected_names:
                path.unlink()
    for name, content in selected_pages.items():
        (pages_dir / name).write_text(content, encoding="utf-8")
    print(f"Generated {len(selected_pages)} site book page(s)")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check", action="store_true", help="fail instead of updating stale output"
    )
    parser.add_argument(
        "--book", metavar="SLUG", help="limit page generation to one site-enabled book"
    )
    args = parser.parse_args()
    try:
        return generate(check=args.check, book=args.book)
    except ValueError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
