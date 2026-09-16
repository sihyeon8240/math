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


def book_lean_metrics(slug: str, root: Path = REPO_ROOT) -> dict[str, int | float]:
    """Return verified, total, and percentage coverage for one textbook."""
    book_dir = root / "books" / slug
    results = [
        labels
        for path in book_dir.rglob("*.tex")
        for labels in theorem_label_groups(path.read_text(encoding="utf-8"))
    ]
    total = len(results)
    errors, proofs = load_proof_index(root)
    if errors:
        raise ValueError("; ".join(errors))
    registered = {
        entry["id"]
        for entry in proofs
        if isinstance(entry, dict)
        and entry.get("book") == slug
        and isinstance(entry.get("id"), str)
        and isinstance(entry.get("declaration"), str)
        and entry["declaration"]
    }
    verified = sum(bool(labels & registered) for labels in results)
    percentage = round(100 * verified / total, 1) if total else 0.0
    return {
        "verified": verified,
        "total": total,
        "percentage": percentage,
    }
