#!/usr/bin/env python3
"""Prepare reviewed version changes and plan post-merge textbook releases."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

import yaml
from book_manifest import load_manifest
from contents_manifest import expected_files

ROOT = Path(__file__).resolve().parent.parent


def version_key(value: str) -> tuple:
    """SemVer precedence, excluding build metadata (unsupported by books.yml)."""
    match = re.fullmatch(
        r"(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)\.(0|[1-9][0-9]*)"
        r"(?:-([0-9A-Za-z-]+(?:\.[0-9A-Za-z-]+)*))?",
        value,
    )
    if not match:
        raise ValueError(f"invalid semantic version: {value}")
    major, minor, patch, suffix = match.groups()
    identifiers = []
    for part in suffix.split(".") if suffix else []:
        if part.isdigit():
            if len(part) > 1 and part.startswith("0"):
                raise ValueError(f"invalid numeric prerelease identifier: {value}")
            identifiers.append((0, int(part)))
        else:
            identifiers.append((1, part))
    return (int(major), int(minor), int(patch), suffix is None, tuple(identifiers))


def plan(previous: dict, current: dict) -> list[str]:
    old = {book["slug"]: book for book in previous["books"]}
    selected = []
    for book in current["books"]:
        before = old.get(book["slug"])
        changed = before is not None and before["version"] != book["version"]
        if changed and version_key(book["version"]) <= version_key(before["version"]):
            raise ValueError(f"version must increase: {book['slug']}")
        enabled_before = before is not None and before.get(
            "release", previous.get("defaults", {}).get("release", False)
        )
        if book["release"] and (changed or not enabled_before):
            version_key(book["version"])
            if not book["build"]:
                raise ValueError(f"release requires build: true: {book['slug']}")
            selected.append(book["slug"])
    return selected


def prepare(book_slug: str, version: str) -> None:
    branch = subprocess.check_output(
        ["git", "branch", "--show-current"], cwd=ROOT, text=True
    ).strip()
    if not branch or branch == "main":
        raise ValueError("prepare releases on local-work or another development branch")
    manifest = load_manifest()
    book = next((b for b in manifest["books"] if b["slug"] == book_slug), None)
    if book is None:
        raise ValueError(f"unknown book: {book_slug}")
    if not book["build"]:
        raise ValueError("release preparation requires build: true")
    requested, current = version_key(version), version_key(book["version"])
    if requested < current or (requested == current and book["release"]):
        raise ValueError(
            "version must increase unless enabling release for the first time"
        )
    path = ROOT / "books.yml"
    text = path.read_text()
    document = yaml.compose(text)
    books_node = next(v for k, v in document.value if k.value == "books")
    node = next(
        item
        for item in books_node.value
        if any(k.value == "slug" and v.value == book_slug for k, v in item.value)
    )
    value = next(v for k, v in node.value if k.value == "version")
    edits = [(value.start_mark.index, value.end_mark.index, version)]
    release = next((v for k, v in node.value if k.value == "release"), None)
    if release is not None:
        edits.append((release.start_mark.index, release.end_mark.index, "true"))
    else:
        # Insert before the version field, respecting its existing indentation.
        key = next(k for k, _ in node.value if k.value == "version")
        position = text.rfind("\n", 0, key.start_mark.index) + 1
        indent = " " * key.start_mark.column
        edits.append((position, position, f"{indent}release: true\n"))
    # Preserve comments, formatting, and unrelated in-progress manifest edits.
    updated = text
    for start, end, replacement in sorted(edits, reverse=True):
        updated = updated[:start] + replacement + updated[end:]
    book = {**book, "version": version, "release": True}
    updates = expected_files(ROOT / "books" / book_slug, "all", book=book)
    updates[path] = updated
    original = {p: p.read_bytes() if p.exists() else None for p in updates}
    try:
        for target, content in updates.items():
            target.write_text(content, encoding="utf-8")
        load_manifest()
    except Exception:
        for target, content in original.items():
            if content is None:
                target.unlink(missing_ok=True)
            else:
                target.write_bytes(content)
        raise
    print(f"Prepared {book_slug} {version}; review and commit the changes in your PR.")
    print(
        "Merging this release preparation authorizes automatic publication after CI passes."
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    prep = sub.add_parser("prepare")
    prep.add_argument("--book", required=True)
    prep.add_argument("--version", required=True)
    planning = sub.add_parser("plan")
    planning.add_argument("--base", required=True)
    args = parser.parse_args()
    try:
        if args.command == "prepare":
            prepare(args.book, args.version)
        else:
            previous = yaml.safe_load(
                subprocess.check_output(
                    ["git", "show", f"{args.base}:books.yml"], cwd=ROOT, text=True
                )
            )
            selected = plan(previous, load_manifest())
            print("matrix=" + json.dumps({"book": selected}, separators=(",", ":")))
            print(f"count={len(selected)}")
        return 0
    except (
        ValueError,
        OSError,
        subprocess.CalledProcessError,
        yaml.YAMLError,
    ) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
