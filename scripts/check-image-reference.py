#!/usr/bin/env python3
"""Validate or update the canonical textbook build image reference."""

from __future__ import annotations

import argparse
import sys

from config_sync import set_image_digest, synchronize
from repository_config import load_image


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--set-digest", metavar="SHA256")
    args = parser.parse_args()
    try:
        if args.set_digest:
            set_image_digest(args.set_digest)
        stale = synchronize(check=True)
        if stale:
            for path in stale:
                print(
                    f"error: synchronized configuration is stale: {path}",
                    file=sys.stderr,
                )
            return 1
        image = load_image()
    except (OSError, UnicodeError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    print(f"Textbook build image is synchronized: {image}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
