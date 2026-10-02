"""Site asset wiring and accessibility contracts, independent of design values."""

from __future__ import annotations

import re
import unittest
from html.parser import HTMLParser
from pathlib import Path

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent


class StylesheetLinks(HTMLParser):
    def __init__(self, document: str) -> None:
        super().__init__()
        self.stylesheets: list[str] = []
        self.has_inline_style = False
        document = re.sub(
            r"{%\s*comment\s*%}.*?{%\s*endcomment\s*%}", "", document, flags=re.DOTALL
        )
        self.feed(document)

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        attributes = dict(attrs)
        if tag == "style":
            self.has_inline_style = True
        if tag == "link" and "stylesheet" in (attributes.get("rel") or "").split():
            self.stylesheets.append(attributes.get("href") or "")


class SiteStylesheetTests(unittest.TestCase):
    def assert_external_stylesheet(self, document_path: Path, asset_path: Path) -> None:
        document = StylesheetLinks(
            (REPO_ROOT / document_path).read_text(encoding="utf-8")
        )
        self.assertFalse(document.has_inline_style)
        asset_url = "/" + asset_path.relative_to("site").as_posix()
        pattern = re.compile(
            r"\{\{\s*(['\"])" + re.escape(asset_url) + r"\1\s*\|\s*relative_url\s*\}\}"
        )
        self.assertTrue(
            any(pattern.fullmatch(href) for href in document.stylesheets),
            f"missing stylesheet link: {asset_url}",
        )
        stylesheet = REPO_ROOT / asset_path
        self.assertTrue(stylesheet.is_file(), f"missing stylesheet: {asset_path}")
        self.assertTrue(self.stylesheet_source(asset_path).strip())

    def stylesheet_source(self, asset_path: Path) -> str:
        source = (REPO_ROOT / asset_path).read_text(encoding="utf-8")
        return re.sub(r"/\*.*?\*/", "", source, flags=re.DOTALL)

    def test_book_layout_uses_dedicated_external_stylesheet(self) -> None:
        self.assertTrue((REPO_ROOT / "site/assets/book.css").is_file())
        layout = (REPO_ROOT / "site/_layouts/book.html").read_text(encoding="utf-8")
        front_matter = yaml.safe_load(layout.split("---", 2)[1])
        self.assertEqual(front_matter["layout"], "default")

    def test_homepage_uses_dedicated_external_stylesheet(self) -> None:
        self.assertTrue((REPO_ROOT / "site/assets/index.css").is_file())
        homepage = (REPO_ROOT / "site/index.html").read_text(encoding="utf-8")
        front_matter = yaml.safe_load(homepage.split("---", 2)[1])
        self.assertEqual(front_matter["stylesheet"], "index")

    def test_pages_use_shared_external_stylesheet(self) -> None:
        self.assert_external_stylesheet(
            Path("site/_layouts/default.html"), Path("site/assets/common.css")
        )

    def test_stylesheets_provide_focus_and_reduced_motion_rules(self) -> None:
        common = self.stylesheet_source(Path("site/assets/common.css"))
        self.assertRegex(common, r":focus-visible[^{}]*\{[^}]+\}")
        self.assertRegex(
            common,
            r"@media\s*\(\s*prefers-reduced-motion\s*:\s*reduce\s*\)\s*\{",
        )

    def test_project_resources_show_lean_coverage(self) -> None:
        layout = (REPO_ROOT / "site/_layouts/book.html").read_text(encoding="utf-8")
        self.assertIn("{{ book.lean_coverage }}%", layout)
        self.assertIn("{{ book.lean_verified }}/{{ book.lean_total }}", layout)


if __name__ == "__main__":
    unittest.main()
