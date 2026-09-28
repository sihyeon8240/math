#!/usr/bin/env python3
"""Generate Lean aggregation modules from the book and topic manifests."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from lean_manifest import ROOT, expected_files, stale_files


def generate(*, root: Path = ROOT, book: str | None = None, check: bool = False) -> int:
    expected = expected_files(root, book)
    stale = stale_files(expected)
    if check and stale:
        for path in stale:
            print(
                f"error: generated Lean assembly is stale: {path.relative_to(root)}",
                file=sys.stderr,
            )
        return 1
    if not check:
        for path in stale:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected[path], encoding="utf-8")
    action = "Validated" if check else "Generated"
    print(f"{action} {len(expected)} Lean aggregation file(s).")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--book")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        return generate(book=args.book, check=args.check)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
