"""Tests for shared lightweight LaTeX scanning."""

from __future__ import annotations

import unittest

from scripts.latex_scan import command_arguments, without_comments


class LatexScanTests(unittest.TestCase):
    def test_comments_and_escaped_percent_are_distinguished(self) -> None:
        text = "visible \\% text % hidden\nnext\n"
        clean = without_comments(text)
        self.assertIn(r"\%", clean)
        self.assertNotIn("hidden", clean)
        self.assertEqual(clean.count("\n"), text.count("\n"))

    def test_commands_allow_whitespace_and_balanced_arguments(self) -> None:
        text = "% \\label{ignored}\n\\label\n {outer-{inner}}\n"
        self.assertEqual(
            [item.argument for item in command_arguments(text, {"label"})],
            ["outer-{inner}"],
        )


if __name__ == "__main__":
    unittest.main()
