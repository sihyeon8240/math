"""Version intent and local preparation regression tests."""

import copy
import importlib
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
releases = importlib.import_module("releases")


class ReleasePlanTests(unittest.TestCase):
    def setUp(self):
        self.old = {
            "books": [
                {"slug": "alpha", "version": "1.0.0", "release": True, "build": True}
            ]
        }
        self.new = copy.deepcopy(self.old)

    def test_content_alone_does_not_release_but_enablement_does(self):
        self.assertEqual(releases.plan(self.old, self.new), [])
        self.old["books"][0]["release"] = False
        self.assertEqual(releases.plan(self.old, self.new), ["alpha"])
        self.assertEqual(releases.plan({"books": []}, self.new), ["alpha"])

    def test_enablement_respects_historical_defaults(self):
        del self.old["books"][0]["release"]
        self.assertEqual(releases.plan(self.old, self.new), ["alpha"])
        self.old["defaults"] = {"release": True}
        self.assertEqual(releases.plan(self.old, self.new), [])
        self.old["defaults"]["release"] = False
        self.assertEqual(releases.plan(self.old, self.new), ["alpha"])

    def test_disabling_and_remaining_disabled_never_publish(self):
        self.new["books"][0]["release"] = False
        self.assertEqual(releases.plan(self.old, self.new), [])
        self.old["books"][0]["release"] = False
        self.assertEqual(releases.plan(self.old, self.new), [])

    def test_enablement_still_rejects_regression_or_disabled_build(self):
        self.old["books"][0]["release"] = False
        self.new["books"][0]["build"] = False
        with self.assertRaises(ValueError):
            releases.plan(self.old, self.new)
        self.new["books"][0].update(build=True, version="0.9.0")
        with self.assertRaises(ValueError):
            releases.plan(self.old, self.new)

    def test_version_increase_selects_only_eligible_books(self):
        self.new["books"][0]["version"] = "1.1.0"
        self.assertEqual(releases.plan(self.old, self.new), ["alpha"])
        self.new["books"][0]["release"] = False
        self.assertEqual(releases.plan(self.old, self.new), [])

    def test_multiple_books_are_selected_independently(self):
        self.old["books"].append({**self.old["books"][0], "slug": "beta"})
        self.new = copy.deepcopy(self.old)
        for book in self.new["books"]:
            book["version"] = "2.0.0"
        self.assertEqual(releases.plan(self.old, self.new), ["alpha", "beta"])

    def test_regression_and_disabled_build_fail(self):
        for version, build in [("0.9.0", True), ("1.1.0", False)]:
            with self.subTest(version=version):
                self.new["books"][0].update(version=version, build=build)
                with self.assertRaises(ValueError):
                    releases.plan(self.old, self.new)

    def test_semver_prerelease_precedence(self):
        ordered = [
            "1.0.0-alpha",
            "1.0.0-alpha.1",
            "1.0.0-beta",
            "1.0.0-rc.2",
            "1.0.0-rc.10",
            "1.0.0",
            "1.0.1",
        ]
        self.assertEqual(sorted(reversed(ordered), key=releases.version_key), ordered)
        for invalid in ["01.0.0", "1.0", "1.0.0-01", "1.0.0;echo bad"]:
            with self.assertRaises(ValueError):
                releases.version_key(invalid)

    def test_prepare_preserves_manifest_comments_and_updates_assembly(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = "# keep this comment\nbooks:\n  - slug: alpha\n    version: '1.0.0' # keep this too\n"
            (root / "books.yml").write_text(source)
            generated = root / "book.tex"
            generated.write_text("old assembly")
            with (
                patch.object(releases, "ROOT", root),
                patch.object(releases, "load_manifest", return_value=self.old),
                patch.object(
                    releases.subprocess, "check_output", return_value="local-work\n"
                ),
                patch.object(
                    releases, "expected_files", return_value={generated: "new assembly"}
                ) as expected,
            ):
                releases.prepare("alpha", "1.1.0")
            self.assertEqual(
                (root / "books.yml").read_text(),
                source.replace(
                    "    version:", "    release: true\n    version:"
                ).replace("'1.0.0'", "1.1.0"),
            )
            self.assertEqual(generated.read_text(), "new assembly")
            self.assertEqual(expected.call_args.kwargs["book"]["version"], "1.1.0")

    def test_prepare_enables_current_version_with_explicit_or_inherited_flag(self):
        self.old["books"][0]["release"] = False
        for field in ["    release: false # retain comment\n", ""]:
            with self.subTest(field=field), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                source = "books:\n  - slug: alpha\n" + field + "    version: 1.0.0\n"
                (root / "books.yml").write_text(source)
                with (
                    patch.object(releases, "ROOT", root),
                    patch.object(releases, "load_manifest", return_value=self.old),
                    patch.object(
                        releases.subprocess, "check_output", return_value="local-work\n"
                    ),
                    patch.object(
                        releases, "expected_files", return_value={}
                    ) as expected,
                ):
                    releases.prepare("alpha", "1.0.0")
                result = (root / "books.yml").read_text()
                self.assertIn("release: true", result)
                self.assertIn("version: 1.0.0", result)
                if field:
                    self.assertIn("# retain comment", result)
                self.assertTrue(expected.call_args.kwargs["book"]["release"])

    def test_prepare_rejects_main_detached_disabled_and_nonincrease(self):
        for branch in ["main\n", "\n"]:
            with patch.object(releases.subprocess, "check_output", return_value=branch):
                with self.assertRaises(ValueError):
                    releases.prepare("alpha", "1.1.0")
        with (
            patch.object(
                releases.subprocess, "check_output", return_value="local-work\n"
            ),
            patch.object(releases, "load_manifest", return_value=self.old),
        ):
            with self.assertRaises(ValueError):
                releases.prepare("alpha", "1.0.0")
            self.old["books"][0]["build"] = False
            with self.assertRaises(ValueError):
                releases.prepare("alpha", "1.1.0")


if __name__ == "__main__":
    unittest.main()
