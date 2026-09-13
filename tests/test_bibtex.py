"""Tests for structural BibTeX key extraction."""

from __future__ import annotations

import unittest

from scripts.bibtex import entry_keys


class BibtexTests(unittest.TestCase):
    def test_extracts_braced_and_parenthesized_entries(self) -> None:
        text = "@book{one, title={One}}\n@article ( two , title={Two})\n"
        self.assertEqual(entry_keys(text), ["one", "two"])

    def test_ignores_non_database_entries(self) -> None:
        text = (
            '@string{journal = "Journal"}\n'
            '@preamble{"prefix"}\n'
            "@comment{not, an entry}\n"
            "@book{real, note={contact a@example.org}}\n"
        )
        self.assertEqual(entry_keys(text), ["real"])

    def test_does_not_treat_at_sign_in_field_value_as_entry(self) -> None:
        text = "@misc{first, note={see @book{fake, title={Nested text}}}}\n"
        self.assertEqual(entry_keys(text), ["first"])

    def test_even_backslashes_do_not_escape_quote_delimiters(self) -> None:
        text = (
            '@misc{first, note="two\\\\", title={done}}\n@book{second, title={Two}}\n'
        )
        self.assertEqual(entry_keys(text), ["first", "second"])


if __name__ == "__main__":
    unittest.main()
