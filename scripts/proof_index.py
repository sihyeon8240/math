"""Load the sharded LaTeX-to-Lean proof index."""

from __future__ import annotations

import re
from pathlib import Path
from typing import Any

import yaml

CHAPTER_RE = re.compile(r"^[0-9]{2}-[a-z0-9]+(?:-[a-z0-9]+)*$")
PROOF_INDEX_DIR = "proof-index"
SHARD_FIELDS = {"book", "chapter", "proofs"}


def load_yaml(path: Path) -> dict[str, Any]:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise ValueError(f"YAML file not found: {path}") from error
    except yaml.YAMLError as error:
        raise ValueError(f"invalid YAML in {path}: {error}") from error
    if not isinstance(data, dict):
        raise ValueError(f"{path} root must be a mapping")
    return data


def load_proof_index(root: Path) -> tuple[list[str], list[dict[str, Any]]]:
    """Load proof shards in deterministic book/chapter order."""
    errors: list[str] = []
    shard_root = root / PROOF_INDEX_DIR
    if not shard_root.is_dir():
        return errors + [f"proof index directory does not exist: {PROOF_INDEX_DIR}"], []

    proofs: list[dict[str, Any]] = []
    for path in sorted(shard_root.rglob("*.yml")):
        relative = path.relative_to(shard_root)
        if len(relative.parts) != 2:
            errors.append(f"proof index shard must be <book>/<chapter>.yml: {relative}")
            continue
        expected_book = relative.parts[0]
        expected_chapter = path.stem
        if not CHAPTER_RE.fullmatch(expected_chapter):
            errors.append(f"proof index shard has invalid chapter name: {relative}")
        try:
            shard = load_yaml(path)
        except ValueError as error:
            errors.append(str(error))
            continue
        unknown = set(shard) - SHARD_FIELDS
        if unknown:
            errors.append(
                f"{relative} contains unknown fields: {', '.join(sorted(unknown))}"
            )
        book = shard.get("book")
        chapter = shard.get("chapter")
        if book != expected_book:
            errors.append(
                f"{relative} book must match its directory: {expected_book!r}"
            )
        if chapter != expected_chapter:
            errors.append(
                f"{relative} chapter must match its filename: {expected_chapter!r}"
            )
        entries = shard.get("proofs")
        if not isinstance(entries, list):
            errors.append(f"{relative} 'proofs' must be a list")
            continue
        for number, entry in enumerate(entries, start=1):
            if not isinstance(entry, dict):
                errors.append(f"{relative} proof entry {number} must be a mapping")
                continue
            shard_owned = {"book", "chapter", "source"} & set(entry)
            if shard_owned:
                errors.append(
                    f"{relative} proof entry {number} contains shard-owned fields: "
                    f"{', '.join(sorted(shard_owned))}"
                )
            enriched = dict(entry)
            enriched["book"] = book
            enriched["chapter"] = chapter
            enriched["source"] = str(relative)
            proofs.append(enriched)
    return errors, proofs
