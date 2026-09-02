"""Compute per-book Lean verification coverage from canonical sources."""

from __future__ import annotations

import re
from pathlib import Path

try:
    from scripts.latex_scan import without_comments
    from scripts.proof_index import load_proof_index
except ModuleNotFoundError:
    from latex_scan import without_comments
    from proof_index import load_proof_index


REPO_ROOT = Path(__file__).resolve().parent.parent
RESULT_ENV_RE = re.compile(r"\\begin\{(?:theorem|lemma|proposition|corollary)\}")


def book_lean_metrics(slug: str, root: Path = REPO_ROOT) -> dict[str, int | float]:
    """Return verified, total, and percentage coverage for one textbook."""
    book_dir = root / "books" / slug
    total = (
        sum(
            len(
                RESULT_ENV_RE.findall(
                    without_comments(path.read_text(encoding="utf-8"))
                )
            )
            for path in book_dir.rglob("*.tex")
        )
        if book_dir.is_dir()
        else 0
    )
    errors, proofs = load_proof_index(root)
    if errors:
        raise ValueError("; ".join(errors))
    verified = sum(
        isinstance(entry, dict) and entry.get("book") == slug for entry in proofs
    )
    if verified > total:
        raise ValueError(
            f"{slug}: proof index has {verified} verified results but "
            f"only {total} theorem environments"
        )
    percentage = round(100 * verified / total, 1) if total else 0.0
    return {
        "verified": verified,
        "total": total,
        "percentage": percentage,
    }
