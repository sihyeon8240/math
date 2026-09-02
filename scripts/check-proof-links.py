#!/usr/bin/env python3
"""Validate the contract between LaTeX theorem labels and Lean declarations."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

try:
    from scripts.proof_index import load_proof_index
except ModuleNotFoundError:
    from proof_index import load_proof_index

try:
    from scripts.book_manifest import load_manifest
    from scripts.latex_scan import command_arguments
except ModuleNotFoundError:
    from book_manifest import load_manifest
    from latex_scan import command_arguments


ROOT = Path(__file__).resolve().parent.parent
LABEL_RE = re.compile(
    r"^[a-z0-9]+:(?:thm|lem|prop|cor):[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*$"
)
DECLARATION_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$")
IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Za-z_][A-Za-z0-9_.']*)")
ALLOWED_FIELDS = {"id", "declaration"}


def index_latex_labels(
    root: Path, books: dict[str, dict[str, Any]]
) -> tuple[list[str], dict[str, Path]]:
    """Map globally unique LaTeX labels to their source files."""
    errors: list[str] = []
    sources: dict[str, Path] = {}
    for slug in sorted(books):
        chapters = root / "books" / slug / "chapters"
        if not chapters.is_dir():
            continue
        for path in sorted(chapters.rglob("*.tex")):
            if path.name == "index.tex":
                continue
            text = path.read_text(encoding="utf-8", errors="replace")
            for label in command_arguments(text, {"label"}):
                previous = sources.get(label.argument)
                if previous is not None:
                    errors.append(
                        f"duplicate LaTeX label {label.argument!r}: "
                        f"{previous.relative_to(root)} and {path.relative_to(root)}"
                    )
                else:
                    sources[label.argument] = path
    return errors, sources


def validate_index(root: Path = ROOT) -> tuple[list[str], list[dict[str, Any]]]:
    errors, proofs = load_proof_index(root)
    try:
        books_data = load_manifest(root / "books.yml", root)
    except ValueError as error:
        return errors + [str(error)], []

    books = {
        book.get("slug"): book
        for book in books_data.get("books", [])
        if isinstance(book, dict) and isinstance(book.get("slug"), str)
    }
    label_errors, label_sources = index_latex_labels(root, books)
    errors.extend(label_errors)
    seen_ids: set[str] = set()
    seen_declarations: set[str] = set()
    valid: list[dict[str, Any]] = []
    for number, entry in enumerate(proofs, start=1):
        source = entry.pop("source")
        chapter = entry.pop("chapter")
        book = entry.pop("book")
        prefix = f"{source} proof entry {number}"
        unknown = set(entry) - ALLOWED_FIELDS
        if unknown:
            errors.append(
                f"{prefix} contains unknown fields: {', '.join(sorted(unknown))}"
            )
        missing = {"id", "declaration"} - set(entry)
        if missing:
            errors.append(f"{prefix} is missing fields: {', '.join(sorted(missing))}")
            continue

        proof_id = entry["id"]
        declaration = entry["declaration"]
        if not isinstance(proof_id, str) or not LABEL_RE.fullmatch(proof_id):
            errors.append(f"{prefix} has invalid theorem label: {proof_id!r}")
        elif proof_id in seen_ids:
            errors.append(f"duplicate proof id: {proof_id}")
        else:
            seen_ids.add(proof_id)
        book_data = books.get(book)
        if book_data is None:
            errors.append(f"{prefix} names an unregistered book: {book!r}")
        else:
            label_prefix = book_data.get("label_prefix")
            owns_label = (
                isinstance(proof_id, str)
                and isinstance(label_prefix, str)
                and proof_id.startswith(f"{label_prefix}:")
            )
            if not owns_label:
                errors.append(
                    f"{prefix} theorem label does not use book prefix "
                    f"{label_prefix!r}: {proof_id!r}"
                )
            lean_module = book_data.get("lean_module")
            expected_namespace = f"Textbooks.{lean_module}."
            owns_declaration = (
                isinstance(declaration, str)
                and isinstance(lean_module, str)
                and declaration.startswith(expected_namespace)
            )
            if not owns_declaration:
                errors.append(
                    f"{prefix} Lean declaration is outside the book namespace "
                    f"{expected_namespace!r}: {declaration!r}"
                )
        if not isinstance(declaration, str) or not DECLARATION_RE.fullmatch(
            declaration
        ):
            errors.append(f"{prefix} has invalid Lean declaration: {declaration!r}")
        elif declaration in seen_declarations:
            errors.append(f"duplicate Lean declaration: {declaration}")
        else:
            seen_declarations.add(declaration)

        tex_path = label_sources.get(proof_id) if isinstance(proof_id, str) else None
        if tex_path is None:
            errors.append(f"{prefix} label is absent from textbook sources")
            continue
        expected_tex_root = root / "books" / str(book) / "chapters" / str(chapter)
        if not tex_path.is_relative_to(expected_tex_root):
            errors.append(
                f"{prefix} label belongs outside shard chapter {chapter!r}: "
                f"{tex_path.relative_to(root)}"
            )
        valid.append(dict(entry, book=book))

    return errors, valid


def check_declarations(root: Path, proofs: list[dict[str, Any]]) -> list[str]:
    if not proofs:
        return []
    output = root / "build" / "lean-links"
    output.mkdir(parents=True, exist_ok=True)
    source = output / "ProofLinks.lean"
    lines = ["import Textbooks", ""]
    lines.extend(f"#check {entry['declaration']}" for entry in proofs)
    source.write_text("\n".join(lines) + "\n", encoding="utf-8")
    result = subprocess.run(
        ["lake", "env", "lean", str(source)],
        cwd=root / "lean",
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode == 0:
        return []
    diagnostic = "\n".join(
        part for part in (result.stdout, result.stderr) if part
    ).strip()
    return [f"Lean declaration check failed:\n{diagnostic}"]


def validate_import_boundaries(root: Path = ROOT) -> list[str]:
    """Keep book modules dependent only on Mathlib and their owning book."""
    errors: list[str] = []
    lean_root = root / "lean"
    textbooks = lean_root / "Textbooks"
    try:
        books_data = load_manifest(root / "books.yml", root)
    except ValueError as error:
        return [str(error)]
    modules = {
        book["lean_module"]
        for book in books_data.get("books", [])
        if isinstance(book, dict) and isinstance(book.get("lean_module"), str)
    }
    root_module = lean_root / "Textbooks.lean"
    if root_module.is_file():
        imported = set(
            re.findall(
                r"(?m)^import Textbooks\.([A-Za-z0-9_]+)\.All$",
                root_module.read_text(encoding="utf-8"),
            )
        )
        for module in sorted(modules - imported):
            errors.append(f"lean/Textbooks.lean does not import Textbooks.{module}.All")
        for module in sorted(imported - modules):
            errors.append(
                f"lean/Textbooks.lean imports unregistered textbook module: {module}"
            )
    else:
        errors.append("missing Lean root module: lean/Textbooks.lean")

    for source in sorted(textbooks.rglob("*.lean")):
        relative = source.relative_to(textbooks)
        owner = relative.parts[0] if len(relative.parts) > 1 else source.stem
        if owner not in modules:
            errors.append(
                f"{source.relative_to(root)} is outside a registered textbook namespace"
            )

    for owner in sorted(modules):
        directory = textbooks / owner
        if not directory.is_dir():
            errors.append(
                f"missing Lean textbook module: {directory.relative_to(root)}"
            )
            continue
        for source in sorted(directory.rglob("*.lean")):
            for number, line in enumerate(
                source.read_text(encoding="utf-8").splitlines(), 1
            ):
                match = re.match(r"\s*import\s+Textbooks\.([A-Za-z0-9_]+)", line)
                if match and match.group(1) != owner:
                    errors.append(
                        f"{source.relative_to(root)}:{number}: direct cross-book import "
                        f"is forbidden: {line.strip()}"
                    )

    local_sources = [root_module] if root_module.is_file() else []
    local_sources.extend(sorted(textbooks.rglob("*.lean")))
    source_by_module = {
        ".".join(source.relative_to(lean_root).with_suffix("").parts): source
        for source in local_sources
    }
    imports = {
        module: set(IMPORT_RE.findall(source.read_text(encoding="utf-8")))
        for module, source in source_by_module.items()
    }
    reachable: set[str] = set()
    pending = ["Textbooks"] if "Textbooks" in source_by_module else []
    while pending:
        module = pending.pop()
        if module in reachable:
            continue
        reachable.add(module)
        pending.extend(
            imported
            for imported in imports.get(module, set())
            if imported in source_by_module and imported not in reachable
        )
    for module in sorted(set(source_by_module) - reachable):
        errors.append(
            f"Lean source is not reachable from Textbooks: "
            f"{source_by_module[module].relative_to(root)}"
        )
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-declarations", action="store_true")
    args = parser.parse_args()
    errors, proofs = validate_index(ROOT)
    errors.extend(validate_import_boundaries(ROOT))
    if args.check_declarations and not errors:
        errors.extend(check_declarations(ROOT, proofs))
    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        return 1
    print(f"Proof index passed ({len(proofs)} verified proof(s)).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
