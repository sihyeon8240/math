"""Deterministic site generation tests."""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path
from unittest import mock

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location(
    "site_generator", REPO_ROOT / "scripts/generate-site-pages.py"
)
assert spec and spec.loader
site_generator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(site_generator)


class SiteGenerationTests(unittest.TestCase):
    def manifest(self) -> dict:
        return {
            "books": [
                {
                    "slug": "alpha",
                    "title": "Alpha",
                    "status": "review",
                    "order": 10,
                    "site": True,
                },
                {
                    "slug": "beta",
                    "title": "Beta",
                    "short_title": "B",
                    "status": "archived",
                    "order": 20,
                    "site": True,
                },
                {
                    "slug": "hidden",
                    "title": "Hidden",
                    "status": "draft",
                    "order": 30,
                    "site": False,
                },
            ]
        }

    def test_status_mapping_and_short_title_fallback(self) -> None:
        books = site_generator.site_books(self.manifest())
        self.assertEqual(
            [book["status_label"] for book in books], ["In Review", "Archived"]
        )
        self.assertEqual(
            [book["display_short_title"] for book in books], ["Alpha", "B"]
        )
        self.assertEqual([book["slug"] for book in books], ["alpha", "beta"])

    def test_site_books_include_lean_coverage(self) -> None:
        metrics = {
            "verified": 2,
            "total": 8,
            "percentage": 25.0,
        }
        with mock.patch.object(
            site_generator, "book_lean_metrics", return_value=metrics
        ):
            books = site_generator.site_books(self.manifest())

        self.assertEqual(books[0]["lean_verified"], 2)
        self.assertEqual(books[0]["lean_total"], 8)
        self.assertEqual(books[0]["lean_coverage"], 25.0)

    def test_all_status_labels(self) -> None:
        self.assertEqual(
            site_generator.STATUS_LABELS,
            {
                "draft": "Draft",
                "review": "In Review",
                "published": "Published",
                "archived": "Archived",
            },
        )

    def test_pages_contain_manifest_derived_metadata(self) -> None:
        pages = site_generator.render_site_pages(self.manifest())
        front_matter = yaml.safe_load(
            pages["alpha.md"].removeprefix("---\n").removesuffix("---\n")
        )
        self.assertEqual(front_matter["layout"], "book")
        self.assertEqual(front_matter["slug"], "alpha")
        self.assertEqual(front_matter["status_label"], "In Review")
        self.assertEqual(front_matter["order"], 10)
        self.assertNotIn("description", pages["alpha.md"].lower())
        self.assertNotIn("hidden.md", pages)

    def test_check_validates_without_writing_pages(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pages_dir = root / "pages"
            with mock.patch.object(
                site_generator,
                "load_manifest",
                return_value=self.manifest(),
            ):
                self.assertEqual(
                    site_generator.generate(check=True, pages_dir=pages_dir), 0
                )
            self.assertFalse(pages_dir.exists())

    def test_single_book_updates_only_selected_page(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            pages_dir = root / "pages"
            pages_dir.mkdir()
            (pages_dir / "beta.md").write_text("unchanged\n", encoding="utf-8")
            with mock.patch.object(
                site_generator, "load_manifest", return_value=self.manifest()
            ):
                self.assertEqual(
                    site_generator.generate(
                        pages_dir=pages_dir,
                        book="alpha",
                    ),
                    0,
                )
            self.assertEqual(
                (pages_dir / "alpha.md").read_text(),
                site_generator.render_site_page(
                    site_generator.site_books(self.manifest())[0]
                ),
            )
            self.assertEqual((pages_dir / "beta.md").read_text(), "unchanged\n")

    def test_single_hidden_book_fails(self) -> None:
        with mock.patch.object(
            site_generator, "load_manifest", return_value=self.manifest()
        ):
            with self.assertRaisesRegex(ValueError, "not enabled for site"):
                site_generator.generate(book="hidden")


if __name__ == "__main__":
    unittest.main()
