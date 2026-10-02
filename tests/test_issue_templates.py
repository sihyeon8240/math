"""Keep textbook choices in GitHub issue forms aligned with books.yml."""

import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent


class IssueTemplateTests(unittest.TestCase):
    def test_issue_book_choices_match_the_manifest(self):
        manifest = yaml.safe_load((ROOT / "books.yml").read_text())
        titles = {book["title"] for book in manifest["books"]}
        for path in (ROOT / ".github/ISSUE_TEMPLATE").glob("*.yml"):
            template = yaml.safe_load(path.read_text())
            for field in template["body"]:
                if field["id"] == "book":
                    with self.subTest(template=path.name):
                        self.assertEqual(set(field["attributes"]["options"]), titles)


if __name__ == "__main__":
    unittest.main()
