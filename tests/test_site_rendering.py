"""Rendered site contracts and optional browser checks using temporary fixtures."""

from __future__ import annotations

import functools
import json
import shutil
import socket
import subprocess
import tempfile
import threading
import time
import unittest
from html.parser import HTMLParser
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from unittest import mock
from urllib.error import URLError
from urllib.parse import urlsplit
from urllib.request import Request, urlopen

import yaml
from test_site_generation import site_generator
from test_support import stop_process_group

REPO_ROOT = Path(__file__).resolve().parent.parent
JEKYLL = shutil.which("jekyll")
BROWSER = shutil.which("chromium") or shutil.which("chromium-browser")
DRIVER = shutil.which("chromedriver")
REVISION = "a" * 40
SPECIAL_TITLE = 'Analysis & "Algebra" <em>Foundations</em>'
SHORT_TITLE = 'A & "B" <i>C</i>'
LONG_TITLE = "Hyper" + "mathematical" * 8 + " Analysis"


class RenderedPage(HTMLParser):
    def __init__(self, source: str) -> None:
        super().__init__()
        self.elements: dict[str, list[dict[str, str | None]]] = {}
        self.text: dict[str, list[str]] = {}
        self.active_text: tuple[str, list[str]] | None = None
        self.feed(source)

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self.elements.setdefault(tag, []).append(dict(attrs))
        if tag in {"title", "h1", "h3", "pre"}:
            self.active_text = (tag, [])

    def handle_data(self, data: str) -> None:
        if self.active_text:
            self.active_text[1].append(data)

    def handle_endtag(self, tag: str) -> None:
        if self.active_text and self.active_text[0] == tag:
            self.text.setdefault(tag, []).append("".join(self.active_text[1]))
            self.active_text = None


class QuietRequestHandler(SimpleHTTPRequestHandler):
    def log_message(self, format: str, *args: object) -> None:
        pass


@unittest.skipUnless(JEKYLL, "Jekyll is required for rendered site tests")
class SiteRenderingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.temporary = tempfile.TemporaryDirectory()
        cls.addClassCleanup(cls.temporary.cleanup)
        cls.workspace = Path(cls.temporary.name)
        cls.source = cls.workspace / "site"
        cls.source.mkdir()
        for directory in ("assets", "_layouts", "_includes"):
            shutil.copytree(REPO_ROOT / "site" / directory, cls.source / directory)
        for filename in ("index.html", "_config.yml"):
            shutil.copyfile(REPO_ROOT / "site" / filename, cls.source / filename)

        cls.books = [
            {
                "slug": "alpha",
                "title": SPECIAL_TITLE,
                "short_title": SHORT_TITLE,
                "status": "draft",
                "order": 20,
                "site": True,
                "release": False,
            },
            {
                "slug": "beta",
                "title": LONG_TITLE,
                "status": "review",
                "order": 10,
                "site": True,
                "release": False,
            },
        ]
        with mock.patch.object(
            site_generator, "snapshot_revision", return_value=REVISION
        ):
            pages = site_generator.render_site_pages({"books": cls.books})
        pages_dir = cls.source / "books"
        pages_dir.mkdir()
        for filename, source in pages.items():
            (pages_dir / filename).write_text(source, encoding="utf-8")
        hidden = {
            "slug": "hidden",
            "title": "Hidden",
            "stylesheet": "book",
            "site": False,
        }
        (pages_dir / "hidden.md").write_text(
            site_generator.render_site_page(hidden), encoding="utf-8"
        )

        cls.config = cls.workspace / "preview.yml"
        cls.config.write_text(
            yaml.safe_dump(
                {
                    "url": "https://example.invalid",
                    "baseurl": "/math",
                    "github": {"repository_url": "https://github.com/example/math"},
                }
            ),
            encoding="utf-8",
        )
        cls.destination = cls.workspace / "rendered"
        cls.build(cls.source, cls.destination)

    @classmethod
    def build(cls, source: Path, destination: Path) -> None:
        result = subprocess.run(
            [
                JEKYLL,
                "build",
                "--source",
                str(source),
                "--destination",
                str(destination),
                "--config",
                f"{source / '_config.yml'},{cls.config}",
                "--disable-disk-cache",
            ],
            cwd=cls.workspace,
            capture_output=True,
            text=True,
            timeout=60,
        )
        if result.returncode:
            raise AssertionError(result.stdout + result.stderr)

    def page(self, path: str) -> RenderedPage:
        return RenderedPage((self.destination / path).read_text(encoding="utf-8"))

    def test_titles_are_escaped_in_text_and_accessible_names(self) -> None:
        home = self.page("index.html")
        detail = self.page("books/alpha.html")
        self.assertEqual(home.text["h3"], [LONG_TITLE, SHORT_TITLE])
        self.assertEqual(detail.text["h1"], [SPECIAL_TITLE])
        self.assertEqual(
            detail.text["title"], [SPECIAL_TITLE + " · Mathematics Textbooks"]
        )
        for page in (home, detail):
            self.assertNotIn("em", page.elements)
            self.assertNotIn("i", page.elements)
        details = [
            link
            for link in home.elements["a"]
            if link.get("href") == "/math/books/alpha.html"
        ]
        self.assertEqual(details[0]["aria-label"], f"View details for {SPECIAL_TITLE}")
        self.assertEqual(
            detail.elements["object"][0]["aria-label"], f"{SPECIAL_TITLE} PDF preview"
        )

    def test_pdf_urls_are_identical_across_all_entry_points(self) -> None:
        home = self.page("index.html")
        detail = self.page("books/alpha.html")
        expected = f"/math/pdf/alpha.pdf?v={REVISION}"
        links = [
            link["href"]
            for page in (home, detail)
            for link in page.elements["a"]
            if "/pdf/alpha.pdf" in (link.get("href") or "")
        ]
        self.assertEqual(links, [expected] * 4)
        self.assertEqual(detail.elements["object"][0]["data"], expected)

    def test_disabled_books_and_releases_are_not_advertised(self) -> None:
        home = self.page("index.html")
        urls = [link.get("href") for link in home.elements["a"]]
        self.assertNotIn("/math/books/hidden.html", urls)
        self.assertNotIn("https://github.com/example/math/releases", urls)

    def test_exported_pages_have_unversioned_pdf_links(self) -> None:
        source = self.workspace / "exported-site"
        shutil.copytree(self.source, source)
        page_path = source / "books" / "alpha.md"
        page_path.write_text(
            page_path.read_text(encoding="utf-8").replace(
                f"snapshot_revision: {REVISION}", "snapshot_revision: ''"
            ),
            encoding="utf-8",
        )
        destination = self.workspace / "exported-rendered"
        self.build(source, destination)
        detail = RenderedPage(
            (destination / "books/alpha.html").read_text(encoding="utf-8")
        )
        self.assertEqual(detail.elements["object"][0]["data"], "/math/pdf/alpha.pdf")

    def test_enabled_releases_link_to_the_release_listing(self) -> None:
        source = self.workspace / "release-site"
        shutil.copytree(self.source, source)
        page_path = source / "books" / "alpha.md"
        page_path.write_text(
            page_path.read_text(encoding="utf-8").replace(
                "release: false", "release: true"
            ),
            encoding="utf-8",
        )
        destination = self.workspace / "release-rendered"
        self.build(source, destination)
        home = RenderedPage((destination / "index.html").read_text(encoding="utf-8"))
        urls = [link.get("href") for link in home.elements["a"]]
        self.assertIn("https://github.com/example/math/releases", urls)
        self.assertNotIn("https://github.com/example/math/releases/latest", urls)

    def test_shared_layout_assets_and_internal_page_links_resolve(self) -> None:
        for path, stylesheet in (("index.html", "index"), ("books/alpha.html", "book")):
            with self.subTest(path=path):
                page = self.page(path)
                self.assertEqual(len(page.elements["html"]), 1)
                self.assertEqual(len(page.elements["main"]), 1)
                self.assertEqual(len(page.elements["footer"]), 1)
                self.assertNotIn("style", page.elements)
                self.assertEqual(
                    [link["href"] for link in page.elements["link"]],
                    ["/math/assets/common.css", f"/math/assets/{stylesheet}.css"],
                )
                for link in page.elements["link"] + page.elements["a"]:
                    url = urlsplit(link.get("href") or "")
                    if not url.path.startswith("/math/") or "/pdf/" in url.path:
                        continue
                    target = self.destination / url.path.removeprefix("/math/")
                    if target.is_dir():
                        target /= "index.html"
                    self.assertTrue(
                        target.is_file(), f"missing link target: {url.path}"
                    )

    @unittest.skipUnless(BROWSER and DRIVER, "Chromium and ChromeDriver are required")
    def test_browser_layout_fits_mobile_tablet_and_desktop(self) -> None:
        web_root = self.workspace / "www"
        shutil.copytree(self.destination, web_root / "math")
        handler = functools.partial(QuietRequestHandler, directory=str(web_root))
        server = ThreadingHTTPServer(("127.0.0.1", 0), handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            self.check_browser_layout(server.server_port)
        finally:
            server.shutdown()
            server.server_close()
            thread.join(timeout=5)

    def check_browser_layout(self, server_port: int) -> None:
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            driver_port = listener.getsockname()[1]
        process = subprocess.Popen(
            [DRIVER, f"--port={driver_port}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
        self.addCleanup(stop_process_group, process)
        driver_url = f"http://127.0.0.1:{driver_port}"

        def request(method: str, path: str, payload: dict | None = None) -> object:
            data = json.dumps(payload).encode() if payload is not None else None
            message = Request(
                driver_url + path,
                data=data,
                method=method,
                headers={"Content-Type": "application/json"},
            )
            with urlopen(message, timeout=30) as response:
                return json.load(response)["value"]

        deadline = time.monotonic() + 10
        while True:
            try:
                request("GET", "/status")
                break
            except URLError:
                if process.poll() is not None or time.monotonic() >= deadline:
                    self.fail("ChromeDriver did not start")
                time.sleep(0.05)

        session = request(
            "POST",
            "/session",
            {
                "capabilities": {
                    "alwaysMatch": {
                        "browserName": "chrome",
                        "goog:chromeOptions": {
                            "binary": BROWSER,
                            "args": [
                                "--headless",
                                "--no-sandbox",
                                "--disable-gpu",
                                "--disable-dev-shm-usage",
                                f"--user-data-dir={self.workspace / 'browser-profile'}",
                            ],
                        },
                    }
                }
            },
        )
        session_path = f"/session/{session['sessionId']}"
        self.addCleanup(request, "DELETE", session_path)
        probe = """
const selectors = "h1, h2, h3, .link-grid, .resource-card, .book-card, .book-card__action";
const overflow = [];
for (const element of document.querySelectorAll(selectors)) {
  const container = element.getBoundingClientRect();
  const bounds = [container];
  if (/^H[123]$/.test(element.tagName)) {
    const range = document.createRange();
    range.selectNodeContents(element);
    const textBounds = [...range.getClientRects()];
    bounds.push(...textBounds);
    if (textBounds.some(rect => rect.left < container.left - 1 || rect.right > container.right + 1)) {
      overflow.push(element.tagName + ":text");
    }
  }
  if (bounds.some(rect => rect.left < -1 || rect.right > innerWidth + 1)) {
    overflow.push(element.tagName + "." + element.className);
  }
}
return {
  width: innerWidth,
  scrollWidth: document.documentElement.scrollWidth,
  overflow,
};
"""
        paths = ("index.html", "books/alpha.html", "books/beta.html")
        for width in (320, 375, 641, 768, 832, 1024, 1440):
            request(
                "POST",
                session_path + "/goog/cdp/execute",
                {
                    "cmd": "Emulation.setDeviceMetricsOverride",
                    "params": {
                        "width": width,
                        "height": 1000,
                        "deviceScaleFactor": 1,
                        "mobile": False,
                    },
                },
            )
            for path in paths:
                with self.subTest(width=width, path=path):
                    request(
                        "POST",
                        session_path + "/url",
                        {"url": f"http://127.0.0.1:{server_port}/math/{path}"},
                    )
                    report = request(
                        "POST",
                        session_path + "/execute/sync",
                        {"script": probe, "args": []},
                    )
                    self.assertEqual(report["width"], width)
                    self.assertLessEqual(report["scrollWidth"], width)
                    self.assertEqual(report["overflow"], [])


if __name__ == "__main__":
    unittest.main()
