"""Check fonts and page breaks through the shared Lean code environment."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TOOLS = ("latexmk", "lualatex", "latexminted")


@unittest.skipUnless(
    all(shutil.which(tool) for tool in TOOLS),
    "Lean rendering checks require latexmk, lualatex, and latexminted",
)
class CodeFontTests(unittest.TestCase):
    def render(self, fixture: str, output: Path) -> Path:
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
                str(ROOT / "tests/fixtures" / f"{fixture}.tex"),
            ],
            cwd=output,
            env=env,
            capture_output=True,
            text=True,
            timeout=180,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        log = output / f"{fixture}.log"
        checked = subprocess.run(
            [sys.executable, str(ROOT / "scripts/check-log.py"), "--strict", str(log)],
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.assertNotIn("LaTeX Font Warning:", log.read_text(encoding="utf-8"))
        self.assertTrue((output / f"{fixture}.pdf").read_bytes().startswith(b"%PDF-"))

        return output / f"{fixture}.aux"

    def test_glyphs_in_regular_italic_bold_and_bold_italic(self) -> None:
        self.render("lean-fonts", ROOT / "build/font-check")

    def test_short_boxes_stay_whole_and_long_boxes_split(self) -> None:
        aux = self.render("lean-page-breaks", ROOT / "build/lean-page-breaks")
        pages = {
            name: int(page)
            for name, page in re.findall(
                r"\\newlabel\{([^}]+)\}\{\{[^}]*\}\{(\d+)\}", aux.read_text()
            )
        }
        for kind in ("short", "long"):
            self.assertGreater(pages[f"{kind}-start"], pages[f"before-{kind}"])

        for kind in ("short", "long", "display"):
            self.assertIn(
                pages[f"{kind}-start"],
                (pages[f"{kind}-prose"], pages[f"{kind}-prose"] + 1),
            )

        self.assertEqual(pages["short-start"], pages["short-end"])
        self.assertEqual(pages["long-start"], pages["long-sixth"])
        self.assertGreater(pages["long-end"], pages["long-start"] + 1)


if __name__ == "__main__":
    unittest.main()
