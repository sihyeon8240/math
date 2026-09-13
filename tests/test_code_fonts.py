"""Render representative Lean glyphs through the actual shared code environment."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLS = ("latexmk", "lualatex", "latexminted")


@unittest.skipUnless(
    all(shutil.which(tool) for tool in TOOLS),
    "the Lean glyph rendering check requires latexmk, lualatex, and latexminted",
)
class CodeFontTests(unittest.TestCase):
    def test_glyphs_in_regular_italic_bold_and_bold_italic(self) -> None:
        # Retain the ignored PDF for visual checks of baselines and fallback widths.
        output = ROOT / "build/font-check"
        output.mkdir(parents=True, exist_ok=True)
        env = os.environ.copy()
        env["TEXINPUTS"] = os.pathsep.join(
            (
                str(ROOT / "common/styles"),
                str(ROOT / "tests/fixtures"),
                env.get("TEXINPUTS", ""),
                "",
            )
        )
        result = subprocess.run(
            [
                "latexmk",
                "-r",
                str(ROOT / "latexmkrc"),
                f"-outdir={output}",
                str(ROOT / "tests/fixtures/lean-fonts.tex"),
            ],
            cwd=output,
            env=env,
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        log = output / "lean-fonts.log"
        checked = subprocess.run(
            [sys.executable, str(ROOT / "scripts/check-log.py"), "--strict", str(log)],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertNotIn("LaTeX Font Warning:", log.read_text(encoding="utf-8"))
        self.assertTrue((output / "lean-fonts.pdf").read_bytes().startswith(b"%PDF-"))


if __name__ == "__main__":
    unittest.main()
