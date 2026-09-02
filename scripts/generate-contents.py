#!/usr/bin/env python3
"""Generate LaTeX textbook assembly from chapters.yml and sections.yml."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from book_manifest import load_manifest
from contents_manifest import expected_files

ROOT = Path(__file__).resolve().parent.parent


def generate(scope: str, *, book: str | None = None, check: bool = False) -> int:
    manifest = load_manifest()
    selected = manifest["books"]
    if book:
        selected = [item for item in selected if item["slug"] == book]
        if not selected:
            raise ValueError(f"book is not registered in books.yml: {book}")

    stale: list[Path] = []
    updates: dict[Path, str] = {}
    for item in selected:
        updates.update(expected_files(ROOT / "books" / item["slug"], scope, book=item))
    for path, expected in updates.items():
        current = path.read_text(encoding="utf-8") if path.is_file() else ""
        if current != expected:
            stale.append(path)
            if not check:
                path.write_text(expected, encoding="utf-8")

    if check and stale:
        for path in stale:
            print(
                f"error: generated contents are stale: {path.relative_to(ROOT)}",
                file=sys.stderr,
            )
        return 1
    action = "Validated" if check else "Generated"
    print(f"{action} {len(updates)} contents file(s).")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("scope", choices=("chap", "sec", "all"))
    parser.add_argument("--book")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        return generate(args.scope, book=args.book, check=args.check)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
