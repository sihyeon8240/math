"""Compute per-book Lean verification coverage from canonical sources."""

from __future__ import annotations

from pathlib import Path

try:
    from scripts.latex_scan import theorem_label_groups
    from scripts.proof_index import load_proof_index
except ModuleNotFoundError:
    from latex_scan import theorem_label_groups
    from proof_index import load_proof_index


REPO_ROOT = Path(__file__).resolve().parent.parent


def registered_results(root: Path = REPO_ROOT) -> dict[str, set[str]]:
    """Load linked result labels once, grouped by textbook."""
    errors, proofs = load_proof_index(root)
    if errors:
        raise ValueError("; ".join(errors))
    registered: dict[str, set[str]] = {}
    for entry in proofs:
        if (
            isinstance(entry.get("book"), str)
            and isinstance(entry.get("id"), str)
            and isinstance(entry.get("declaration"), str)
            and entry["declaration"]
        ):
            registered.setdefault(entry["book"], set()).add(entry["id"])
    return registered


def result_metrics(
    results: list[set[str]], registered: set[str]
) -> dict[str, int | float]:
    """Count each result once, even when it has multiple linked labels."""
    total = len(results)
    verified = sum(bool(labels & registered) for labels in results)
    percentage = round(100 * verified / total, 1) if total else 0.0
    return {"verified": verified, "total": total, "percentage": percentage}


def book_lean_metrics(
    slug: str,
    root: Path = REPO_ROOT,
    *,
    registered: dict[str, set[str]] | None = None,
) -> dict[str, int | float]:
    """Return coverage, optionally reusing a caller's repository-wide index."""
    book_dir = root / "books" / slug
    results = [
        labels
        for path in book_dir.rglob("*.tex")
        for labels in theorem_label_groups(path.read_text(encoding="utf-8"))
    ]
    if registered is None:
        registered = registered_results(root)
    return result_metrics(results, registered.get(slug, set()))
