#!/usr/bin/env python3
"""Validate label structure without rewriting legacy identifiers."""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

from book_manifest import load_manifest
from latex_scan import command_arguments

KIND = r"(ch|sec|ax|def|thm|lem|prop|cor|ex|exc|prob|eq|fig|tab)"
PLACEHOLDER = re.compile(r"^xx:(ch|sec):[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*$")


def book_for(path: Path) -> str | None:
    parts = path.as_posix().split("/")
    try:
        return parts[parts.index("books") + 1]
    except (ValueError, IndexError):
        return None


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+", type=Path)
    args = parser.parse_args()

    manifest = load_manifest()
    expected = {book["slug"]: book["label_prefix"] for book in manifest["books"]}
    prefixes = "|".join(re.escape(prefix) for prefix in sorted(expected.values()))
    modern = re.compile(rf"^(?:{prefixes}):{KIND}:[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*")

    seen: dict[str, tuple[Path, int]] = {}
    legacy: dict[str, list[tuple[str, str]]] = defaultdict(list)
    failed = False

    for path in args.files:
        text = path.read_text(
            encoding="utf-8",
            errors="replace",
        )
        for match in command_arguments(text, {"label"}):
            label = match.argument
            lineno = text.count("\n", 0, match.position) + 1
            where = f"{path}:{lineno}"

            if not label:
                print(
                    f"{where}: error: empty label",
                    file=sys.stderr,
                )
                failed = True
                continue

            if any(character.isspace() for character in label):
                print(
                    f"{where}: error: whitespace in label '{label}'",
                    file=sys.stderr,
                )
                failed = True

            if label in seen:
                old_path, old_line = seen[label]
                print(
                    f"{where}: error: duplicate label '{label}' "
                    f"(first at {old_path}:{old_line})",
                    file=sys.stderr,
                )
                failed = True
            else:
                seen[label] = (path, lineno)

            if modern.fullmatch(label):
                book = book_for(path)
                book_prefix = expected.get(book)
                if book_prefix and not label.startswith(book_prefix + ":"):
                    print(
                        f"{where}: error: prefix collision for "
                        f"'{label}', expected '{book_prefix}:'",
                        file=sys.stderr,
                    )
                    failed = True
            elif PLACEHOLDER.fullmatch(label) and "common/templates" in path.as_posix():
                pass
            else:
                legacy[book_for(path) or "shared"].append((where, label))

    for book, entries in sorted(legacy.items()):
        for where, label in entries:
            print(
                f"{where}: warning: legacy label '{label}' does not follow "
                "<book>:<kind>:<description>",
                file=sys.stderr,
            )
        print(
            f"warning: {book}: {len(entries)} legacy labels do not yet follow "
            "<book>:<kind>:<description>",
            file=sys.stderr,
        )

    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
