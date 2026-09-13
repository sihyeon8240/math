"""Manifest normalization, validation, export, and diagnostic tests."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import book_manifest as books_module  # noqa: E402
from book_manifest import load_manifest, manifest_warnings  # noqa: E402


class ManifestWarningTests(unittest.TestCase):
    def test_status_labels_are_the_status_schema(self) -> None:
        self.assertEqual(
            books_module.ALLOWED_STATUSES, frozenset(books_module.STATUS_LABELS)
        )

    def test_suspicious_combinations_are_warnings(self) -> None:
        manifest = {
            "books": [
                {
                    "slug": "archived-a",
                    "status": "archived",
                    "order": 10,
                    "release": True,
                    "site": True,
                },
                {
                    "slug": "draft-b",
                    "status": "draft",
                    "order": 10,
                    "release": True,
                    "site": False,
                },
            ]
        }

        warnings = manifest_warnings(manifest)

        self.assertEqual(len(warnings), 4)
        self.assertTrue(any("duplicate order 10" in warning for warning in warnings))
        self.assertTrue(
            any("archived but release=true" in warning for warning in warnings)
        )
        self.assertTrue(
            any("archived but site=true" in warning for warning in warnings)
        )
        self.assertTrue(
            any("draft but release=true" in warning for warning in warnings)
        )

    def test_current_style_configuration_has_no_warnings(self) -> None:
        manifest = {
            "books": [
                {
                    "slug": "published",
                    "status": "published",
                    "order": 10,
                    "release": True,
                    "site": True,
                },
                {
                    "slug": "draft",
                    "status": "draft",
                    "order": 20,
                    "release": False,
                    "site": False,
                },
            ]
        }

        self.assertEqual(manifest_warnings(manifest), [])


class ManifestModuleTests(unittest.TestCase):
    def fixture(
        self, book: dict[str, object], defaults: dict[str, object] | None = None
    ):
        temporary = tempfile.TemporaryDirectory()
        root = Path(temporary.name)
        book = {"version": "1.0.0", **book}
        slug = str(book.get("slug", "sample"))
        book_dir = root / "books" / slug
        book_dir.mkdir(parents=True)
        (book_dir / "book.tex").write_text("", encoding="utf-8")
        manifest_path = root / "books.yml"
        manifest_path.write_text(
            yaml.safe_dump(
                {
                    "schema_version": 1,
                    "defaults": defaults
                    or {
                        "author": "Sample Author",
                        "build": True,
                        "check": False,
                        "release": False,
                        "site": True,
                    },
                    "books": [book],
                },
                sort_keys=False,
            ),
            encoding="utf-8",
        )
        self.addCleanup(temporary.cleanup)
        return root, manifest_path, book_dir

    def test_load_manifest_merges_defaults_and_sorts(self) -> None:
        root, path, _ = self.fixture(
            {
                "slug": "sample",
                "title": "Sample",
                "status": "draft",
                "order": 10,
                "check": True,
            }
        )
        book = load_manifest(path, root)["books"][0]
        self.assertTrue(book["build"])
        self.assertTrue(book["check"])
        self.assertFalse(book["release"])
        self.assertTrue(book["site"])

    def test_load_manifest_rejects_invalid_fields(self) -> None:
        for override, diagnostic in (
            ({"unknown": 1}, "unknown field"),
            ({"build": "yes"}, "must be boolean"),
            ({"version": "1.0"}, "invalid version"),
            ({"author": ""}, "author"),
        ):
            with self.subTest(override=override):
                book = {
                    "slug": "sample",
                    "title": "Sample",
                    "status": "draft",
                    "order": 10,
                    **override,
                }
                root, path, _ = self.fixture(book)
                with self.assertRaisesRegex(ValueError, diagnostic):
                    load_manifest(path, root)


class ManifestFixture(unittest.TestCase):
    def make_repository(
        self,
        records: list[dict],
    ) -> tuple[Path, Path]:
        root = Path(self.directory.name)
        for record in records:
            slug = record["slug"]
            book_dir = root / "books" / slug
            book_dir.mkdir(parents=True, exist_ok=True)
            (book_dir / "book.tex").write_text("", encoding="utf-8")
        manifest = {
            "schema_version": 1,
            "defaults": {
                "author": "Sample Author",
                "build": True,
                "check": True,
                "release": False,
                "site": False,
            },
            "books": records,
        }
        path = root / "books.yml"
        path.write_text(yaml.safe_dump(manifest, sort_keys=False), encoding="utf-8")
        return root, path

    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()

    def tearDown(self) -> None:
        self.directory.cleanup()


class ManifestRecordTests(ManifestFixture):
    def base(self, slug: str, **overrides: object) -> dict:
        record = {
            "slug": slug,
            "title": slug.title(),
            "version": "1.0.0",
            "status": "draft",
            "order": 10,
        }
        record.update(overrides)
        return record

    def load(self, root: Path, path: Path) -> dict:
        return books_module.load_manifest(path, root)

    def test_site_filter_and_order_then_slug(self) -> None:
        records = [
            self.base("zeta", order=20, site=False),
            self.base("beta", order=10, site=True),
            self.base("alpha", order=10, site=True),
        ]
        root, path = self.make_repository(records)
        manifest = self.load(root, path)
        self.assertEqual(
            [book["slug"] for book in manifest["books"]], ["alpha", "beta", "zeta"]
        )

    def test_unknown_status_is_rejected(self) -> None:
        root, path = self.make_repository([self.base("alpha", status="unknown")])
        with self.assertRaisesRegex(ValueError, "invalid status"):
            self.load(root, path)

    def test_matching_slug_succeeds(self) -> None:
        root, path = self.make_repository([self.base("alpha")])
        manifest = self.load(root, path)
        self.assertEqual(manifest["books"][0]["slug"], "alpha")


class SiteManifestValidationTests(unittest.TestCase):
    def load(self, *, defaults_build: bool = True, build=None, site=False):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            book_dir = root / "books" / "alpha"
            book_dir.mkdir(parents=True)
            (book_dir / "book.tex").write_text("", encoding="utf-8")
            record = {
                "slug": "alpha",
                "title": "Alpha",
                "version": "1.0.0",
                "status": "draft",
                "order": 10,
                "site": site,
            }
            if build is not None:
                record["build"] = build
            manifest = {
                "schema_version": 1,
                "defaults": {
                    "author": "Sample Author",
                    "build": defaults_build,
                    "check": True,
                    "release": False,
                    "site": False,
                },
                "books": [record],
            }
            path = root / "books.yml"
            path.write_text(yaml.safe_dump(manifest), encoding="utf-8")
            return load_manifest(path, root)

    def test_site_and_build_true_succeeds(self):
        manifest = self.load(build=True, site=True)
        self.assertTrue(manifest["books"][0]["build"])
        self.assertTrue(manifest["books"][0]["site"])

    def test_site_and_build_false_succeeds_when_site_is_false(self):
        self.load(build=False, site=False)

    def test_site_true_and_build_false_fails(self):
        with self.assertRaisesRegex(
            ValueError, "book 'alpha' cannot have site=true when build=false"
        ):
            self.load(build=False, site=True)

    def test_default_build_false_and_site_true_fails(self):
        with self.assertRaisesRegex(ValueError, "site=true when build=false"):
            self.load(defaults_build=False, site=True)

    def test_book_can_override_default_build_for_site(self):
        manifest = self.load(defaults_build=False, build=True, site=True)
        self.assertTrue(manifest["books"][0]["build"])
        self.assertTrue(manifest["books"][0]["site"])


if __name__ == "__main__":
    unittest.main()
