#!/usr/bin/env python3
"""Validate the contract between LaTeX theorem labels and Lean declarations."""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

import yaml

try:
    from scripts.proof_index import load_proof_index
except ModuleNotFoundError:
    from proof_index import load_proof_index


ROOT = Path(__file__).resolve().parent.parent
LABEL_RE = re.compile(
    r"^[a-z0-9]+:(?:thm|lem|prop|cor):[A-Za-z0-9]+(?:-[A-Za-z0-9]+)*$"
)
DECLARATION_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$")
MARKER_RE = re.compile(r"\\leanverified\{([^{}]+)\}")
IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Za-z_][A-Za-z0-9_.']*)")
ALLOWED_FIELDS = {"id", "tex", "declaration", "foundations"}


def load_yaml(path: Path) -> dict[str, Any]:
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise ValueError(f"manifest not found: {path}") from error
    except yaml.YAMLError as error:
        raise ValueError(f"invalid YAML in {path}: {error}") from error
    if not isinstance(data, dict):
        raise ValueError(f"{path.name} root must be a mapping")
    return data


def validate_index(root: Path = ROOT) -> tuple[list[str], list[dict[str, Any]]]:
    errors, proofs = load_proof_index(root)
    try:
        books_data = load_yaml(root / "books.yml")
    except ValueError as error:
        return errors + [str(error)], []

    books = {
        book.get("slug"): book
        for book in books_data.get("books", [])
        if isinstance(book, dict) and isinstance(book.get("slug"), str)
    }
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
        missing = {"id", "tex", "declaration"} - set(entry)
        if missing:
            errors.append(f"{prefix} is missing fields: {', '.join(sorted(missing))}")
            continue

        proof_id = entry["id"]
        tex = entry["tex"]
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

        if (
            not isinstance(tex, str)
            or Path(tex).is_absolute()
            or ".." in Path(tex).parts
        ):
            errors.append(f"{prefix} has an unsafe TeX path: {tex!r}")
            continue
        expected_tex_root = Path("chapters") / str(chapter)
        if not Path(tex).is_relative_to(expected_tex_root):
            errors.append(
                f"{prefix} TeX path is outside shard chapter {chapter!r}: {tex!r}"
            )
        tex_path = root / "books" / str(book) / tex
        try:
            text = tex_path.read_text(encoding="utf-8")
        except (FileNotFoundError, IsADirectoryError):
            errors.append(f"{prefix} TeX file does not exist: books/{book}/{tex}")
            continue
        if rf"\label{{{proof_id}}}" not in text:
            errors.append(f"{prefix} label is absent from books/{book}/{tex}")
        if rf"\leanverified{{{proof_id}}}" not in text:
            errors.append(
                f"{prefix} verification marker is absent from books/{book}/{tex}"
            )

        foundations = entry.get("foundations", [])
        if not isinstance(foundations, list) or not all(
            isinstance(item, str) and item for item in foundations
        ):
            errors.append(f"{prefix} foundations must be a list of non-empty strings")
        valid.append(dict(entry, book=book))

    indexed_ids = {
        entry.get("id") for entry in valid if isinstance(entry.get("id"), str)
    }
    marker_locations: dict[str, list[Path]] = {}
    for slug in sorted(books):
        book_dir = root / "books" / slug
        if not book_dir.is_dir():
            continue
        for tex_path in sorted(book_dir.rglob("*.tex")):
            text = tex_path.read_text(encoding="utf-8")
            for marker_id in MARKER_RE.findall(text):
                marker_locations.setdefault(marker_id, []).append(tex_path)
    for marker_id, locations in sorted(marker_locations.items()):
        if marker_id not in indexed_ids:
            errors.append(f"unregistered Lean verification marker: {marker_id}")
        if len(locations) > 1:
            rendered = ", ".join(str(path.relative_to(root)) for path in locations)
            errors.append(f"duplicate Lean verification marker {marker_id}: {rendered}")
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
    """Keep book modules dependent only on Mathlib and Foundation by default."""
    errors: list[str] = []
    lean_root = root / "lean"
    textbooks = lean_root / "Textbooks"
    try:
        books_data = load_yaml(root / "books.yml")
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
                if match and match.group(1) not in {"Foundation", owner}:
                    errors.append(
                        f"{source.relative_to(root)}:{number}: direct cross-book import "
                        f"is forbidden: {line.strip()}"
                    )
    foundation_sources = []
    foundation_root = textbooks / "Foundation.lean"
    if foundation_root.is_file():
        foundation_sources.append(foundation_root)
    foundation_directory = textbooks / "Foundation"
    if foundation_directory.is_dir():
        foundation_sources.extend(sorted(foundation_directory.rglob("*.lean")))
    for source in foundation_sources:
        for number, line in enumerate(
            source.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = re.match(r"\s*import\s+Textbooks\.([A-Za-z0-9_]+)", line)
            if match and match.group(1) != "Foundation":
                errors.append(
                    f"{source.relative_to(root)}:{number}: Foundation may not import "
                    f"a textbook module: {line.strip()}"
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
