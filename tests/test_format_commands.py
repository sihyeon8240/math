"""Formatter argument handling and source preservation."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from test_support import write_executable

ROOT = Path(__file__).resolve().parent.parent


class FormatterArgumentsTests(unittest.TestCase):
    def test_extra_check_arguments_are_rejected_before_running_tools(self) -> None:
        for name in ("python", "shell", "tex"):
            with self.subTest(formatter=name):
                result = subprocess.run(
                    [str(ROOT / f"scripts/format-{name}.sh"), "--check", "extra"],
                    cwd=ROOT,
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=10,
                )
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("usage:", result.stderr)


class FormatTexTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("latexindent"), "latexindent is required")
    def test_wraps_prose_to_100_columns_and_preserves_lean(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            (root / "config").mkdir()
            shutil.copy2(
                ROOT / "config/latexindent.yaml", root / "config/latexindent.yaml"
            )
            for name in ("format-tex.sh", "normalize-eof.sh"):
                shutil.copy2(ROOT / "scripts" / name, scripts / name)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, timeout=30)
            sentence = (
                "A mathematical explanation "
                + "with enough detail to require several source lines " * 4
                + "and an inline formula $a=qb+r$."
            )
            prose = (sentence + " ") * 3
            lean = "    -- " + "Preserve this long Lean comment. " * 5 + "\n"
            source = (
                "\\begin{proof} \\label{test:proof}\n"
                + "  "
                + prose.rstrip()
                + "\n\n"
                + "  \\begin{lean}\n"
                + lean
                + "    example : True := by\n      trivial\n"
                + "  \\end{lean}\n\\end{proof}\n"
            )
            path = root / "proof.tex"
            path.write_text(source, encoding="utf-8")
            subprocess.run(
                ["git", "add", "proof.tex"], cwd=root, check=True, timeout=30
            )

            def run(*arguments: str) -> subprocess.CompletedProcess[str]:
                return subprocess.run(
                    [str(scripts / "format-tex.sh"), *arguments],
                    cwd=root,
                    env={**os.environ, "FORMAT_TEX_CACHE_DIR": str(root / "cache")},
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=30,
                )

            result = run("--check")
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertEqual(path.read_text(), source)
            result = run()
            self.assertEqual(result.returncode, 0, result.stderr)
            formatted = path.read_text()
            paragraph = formatted.split("\n\n")[0].split("\n", 2)[2]
            self.assertEqual(" ".join(paragraph.split()), prose.strip())
            self.assertGreater(len(paragraph.splitlines()), 3)
            self.assertEqual(paragraph.count("\n  A mathematical explanation"), 2)
            for line in paragraph.splitlines():
                self.assertLessEqual(len(line), 100)
                self.assertTrue(line.startswith("  "))
            self.assertIn(lean, formatted)
            for arguments in [("--check",), ()]:
                shutil.rmtree(root / "cache")
                result = run(*arguments)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(path.read_text(), formatted)
            # Changing the wrap width must invalidate a successful cached check.
            settings = root / "config/latexindent.yaml"
            settings.write_text(
                settings.read_text().replace("columns: 100", "columns: 60")
            )
            result = run("--check")
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertEqual(path.read_text(), formatted)

    @unittest.skipUnless(shutil.which("latexindent"), "latexindent is required")
    def test_wraps_comments_but_preserves_metadata_and_display_math(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            (root / "config").mkdir()
            shutil.copy2(
                ROOT / "config/latexindent.yaml", root / "config/latexindent.yaml"
            )
            for name in ("format-tex.sh", "normalize-eof.sh"):
                shutil.copy2(ROOT / "scripts" / name, scripts / name)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, timeout=30)
            metadata = (
                "% !TEX root = book.tex\n"
                "% BEGIN GENERATED APPENDICES\n"
                "% END GENERATED APPENDICES\n"
                "% Lean source: " + "Textbooks.LongModule." * 8 + "result\n%\n"
            )
            comment = "An explanatory comment " + "with useful context " * 12
            display = "  \\[\n    a=qb+r.\n  \\]\n"
            source = (
                metadata + "\n\\begin{proof} First sentence. Second sentence.\n"
                "% " + comment.strip() + "\n"
                "  The following identity holds:\n" + display + "\\end{proof}\n"
            )
            path = root / "proof.tex"
            path.write_text(source)
            subprocess.run(
                ["git", "add", "proof.tex"], cwd=root, check=True, timeout=30
            )

            def run(*arguments: str) -> subprocess.CompletedProcess[str]:
                return subprocess.run(
                    [str(scripts / "format-tex.sh"), *arguments],
                    cwd=root,
                    env={**os.environ, "FORMAT_TEX_CACHE_DIR": str(root / "cache")},
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=30,
                )

            result = run()
            self.assertEqual(result.returncode, 0, result.stderr)
            formatted = path.read_text()
            self.assertTrue(formatted.startswith(metadata))
            self.assertIn(
                "\\begin{proof}\n  First sentence.\n  Second sentence.\n", formatted
            )
            self.assertIn(display, formatted)
            body = formatted[len(metadata) :]
            comments = [
                line for line in body.splitlines() if line.lstrip().startswith("%")
            ]
            self.assertGreater(len(comments), 1)
            self.assertEqual(
                " ".join(line.lstrip()[1:].strip() for line in comments),
                comment.strip(),
            )
            self.assertTrue(all(len(line) <= 100 for line in comments))
            shutil.rmtree(root / "cache")
            result = run("--check")
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(path.read_text(), formatted)

    @unittest.skipUnless(shutil.which("latexindent"), "latexindent is required")
    def test_lean_indentation_preserves_relative_offsets(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            (root / "config").mkdir()
            shutil.copy2(
                ROOT / "config/latexindent.yaml", root / "config/latexindent.yaml"
            )
            for name in ("format-tex.sh", "normalize-eof.sh"):
                shutil.copy2(ROOT / "scripts" / name, scripts / name)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, timeout=30)
            body = "  classical\n  have h : 0 ≤ a := by\n    nlinarith\n"
            source = (
                "\\begin{proof}\n"
                "  Since $b$ is positive, $1\\le b$.\n\n"
                "  \\begin{lean}\n" + body + "\\end{lean} % keep comment\n"
                "  Already aligned.\n\n"
                "  \\begin{lean}\n"
                "    exact h\n"
                "  \\end{lean}\n"
                "\\end{proof}\n"
            )
            expected = source.replace("\n\\end{lean} %", "\n  \\end{lean} %")
            expected = expected.replace(
                "  classical\n  have h : 0 ≤ a := by\n    nlinarith\n",
                "    classical\n    have h : 0 ≤ a := by\n      nlinarith\n",
            )
            # Preserve relative indentation for definitions, proofs, and blank lines.
            extra = (
                "An $\\{x\\}$ and \\textbf{nested} explanation.\n\n"
                "\\begin{lean} % code only\n"
                "abbrev neighborhood (p : X) (r : ℝ) : Set X := ball p r\n"
                "\n"
                "example : True := by\n"
                "  trivial\n"
                "\\end{lean}\n"
                "Over-indented.\n\n"
                "\\begin{lean}\n"
                "        example : True := by\n"
                "          trivial\n"
                "\\end{lean}\n"
                "Empty.\n\n"
                "\\begin{lean}\n"
                "\\end{lean}\n"
            )
            source += extra
            expected += (
                extra.replace("\nabbrev", "\n  abbrev")
                .replace("\nexample", "\n  example")
                .replace("\n  trivial", "\n    trivial")
                .replace("\n        example", "\n  example")
                .replace("\n          trivial", "\n    trivial")
            )
            path = root / "proof.tex"
            path.write_text(source, encoding="utf-8")
            subprocess.run(
                ["git", "add", "proof.tex"], cwd=root, check=True, timeout=30
            )

            def run(*arguments: str) -> subprocess.CompletedProcess[str]:
                return subprocess.run(
                    [str(scripts / "format-tex.sh"), *arguments],
                    cwd=root,
                    env={**os.environ, "FORMAT_TEX_CACHE_DIR": str(root / "cache")},
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=30,
                )

            result = run("--check")
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertEqual(path.read_text(encoding="utf-8"), source)
            result = run()
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(path.read_text(encoding="utf-8"), expected)
            shutil.rmtree(root / "cache")
            result = run("--check")
            self.assertEqual(result.returncode, 0, result.stderr)
            shutil.rmtree(root / "cache")
            result = run()
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(path.read_text(encoding="utf-8"), expected)

    @unittest.skipUnless(shutil.which("latexindent"), "latexindent is required")
    def test_prose_and_code_indentation_are_checked_independently(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            (root / "config").mkdir()
            shutil.copy2(
                ROOT / "config/latexindent.yaml", root / "config/latexindent.yaml"
            )
            for name in ("format-tex.sh", "normalize-eof.sh"):
                shutil.copy2(ROOT / "scripts" / name, scripts / name)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, timeout=30)
            source = (
                "\\begin{theorem}\n"
                "Suppose $a\\in\\Z$. % unmatched { in a comment\n"
                "Use \\textbf{nested {braces}} and $\\{a\\}$.\n"
                "\\[\n"
                "  a=a.\n"
                "\\]\n"
                "\n"
                "  \\begin{lean}\n"
                "    example (a : ℤ) : a = a := by\n"
                "      rfl\n"
                "  \\end{lean}\n"
                "\\end{theorem}\n"
            )
            expected = source.replace(
                "Suppose $a\\in\\Z$. % unmatched { in a comment\n"
                "Use \\textbf{nested {braces}} and $\\{a\\}$.\n"
                "\\[\n"
                "  a=a.\n"
                "\\]\n"
                "\n",
                "  Suppose $a\\in\\Z$.\n"
                "  % unmatched { in a comment\n"
                "  Use \\textbf{nested {braces}} and $\\{a\\}$.\n"
                "  \\[\n"
                "    a=a.\n"
                "  \\]\n"
                "\n",
            )
            path = root / "theorem.tex"
            path.write_text(source, encoding="utf-8")
            subprocess.run(
                ["git", "add", "theorem.tex"], cwd=root, check=True, timeout=30
            )

            def run(*arguments: str) -> subprocess.CompletedProcess[str]:
                return subprocess.run(
                    [str(scripts / "format-tex.sh"), *arguments],
                    cwd=root,
                    env={**os.environ, "FORMAT_TEX_CACHE_DIR": str(root / "cache")},
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=30,
                )

            result = run("--check")
            self.assertEqual(result.returncode, 1, result.stderr)
            self.assertEqual(path.read_text(), source)
            result = run()
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(path.read_text(), expected)
            # A fresh check and second formatting pass must agree without cache.
            for arguments in [("--check",), ()]:
                shutil.rmtree(root / "cache")
                result = run(*arguments)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(path.read_text(), expected)
            # A Lean indentation change must invalidate the cached success.
            path.write_text(expected.replace("  \\end{lean}\n", "\\end{lean}\n"))
            result = run("--check")
            self.assertEqual(result.returncode, 1, result.stderr)

    def test_only_tracked_tex_files_are_checked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            (root / "config").mkdir()
            shutil.copy2(
                ROOT / "config/latexindent.yaml", root / "config/latexindent.yaml"
            )
            shutil.copy2(ROOT / "scripts/format-tex.sh", scripts / "format-tex.sh")
            shutil.copy2(
                ROOT / "scripts/normalize-eof.sh", scripts / "normalize-eof.sh"
            )
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, timeout=30)
            (root / "tracked.tex").write_text("tracked\n", encoding="utf-8")
            (root / "draft.tex").write_text("draft\n", encoding="utf-8")
            subprocess.run(
                ["git", "add", "tracked.tex"], cwd=root, check=True, timeout=30
            )

            binary = root / "bin"
            binary.mkdir()
            latexindent = binary / "latexindent"
            write_executable(
                latexindent,
                "#!/usr/bin/env python3\n"
                "import os\n"
                "import pathlib\n"
                "import sys\n"
                'if "--version" in sys.argv:\n'
                '    print("latexindent fake")\n'
                "    raise SystemExit(0)\n"
                'capture = pathlib.Path(os.environ["FORMAT_TEX_CAPTURE"])\n'
                'with capture.open("a", encoding="utf-8") as stream:\n'
                "    for argument in sys.argv[1:]:\n"
                '        if argument.endswith((".tex", ".sty")):\n'
                '            stream.write(argument + "\\n")\n'
                '            print(pathlib.Path(argument).read_text(), end="")\n',
            )
            capture = root / "capture.txt"
            result = subprocess.run(
                [str(scripts / "format-tex.sh"), "--check"],
                cwd=root,
                env={
                    **os.environ,
                    "PATH": f"{binary}:{os.environ['PATH']}",
                    "FORMAT_TEX_CAPTURE": str(capture),
                    "FORMAT_TEX_CACHE_DIR": str(root / "cache"),
                },
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            inputs = capture.read_text(encoding="utf-8").splitlines()
            self.assertEqual(len(inputs), 2)
            self.assertEqual(inputs[0], "tracked.tex")
            self.assertEqual(Path(inputs[1]).name, "wrapped.tex")


class FormatShellTests(unittest.TestCase):
    def test_only_repository_shell_scripts_are_checked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(ROOT / "scripts/format-shell.sh", scripts / "format-shell.sh")
            shutil.copy2(
                ROOT / "scripts/normalize-eof.sh", scripts / "normalize-eof.sh"
            )
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, timeout=30)
            (scripts / "tracked.sh").write_text(
                "#!/usr/bin/env bash\n", encoding="utf-8"
            )
            (scripts / "draft.sh").write_text("#!/usr/bin/env bash\n", encoding="utf-8")
            (root / "outside.sh").write_text("#!/usr/bin/env bash\n", encoding="utf-8")
            subprocess.run(
                ["git", "add", "scripts/tracked.sh"], cwd=root, check=True, timeout=30
            )

            binary = root / "bin"
            binary.mkdir()
            shfmt = binary / "shfmt"
            write_executable(
                shfmt,
                "#!/usr/bin/env python3\n"
                "import os\n"
                "import pathlib\n"
                "import sys\n"
                'capture = pathlib.Path(os.environ["FORMAT_SHELL_CAPTURE"])\n'
                'with capture.open("w", encoding="utf-8") as stream:\n'
                "    for argument in sys.argv[1:]:\n"
                '        if argument.endswith(".sh"):\n'
                '            stream.write(argument + "\\n")\n',
            )
            capture = root / "capture.txt"
            result = subprocess.run(
                [str(scripts / "format-shell.sh"), "--check"],
                cwd=root,
                env={
                    **os.environ,
                    "PATH": f"{binary}:{os.environ['PATH']}",
                    "FORMAT_SHELL_CAPTURE": str(capture),
                },
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(
                set(capture.read_text(encoding="utf-8").splitlines()),
                {
                    "scripts/draft.sh",
                    "scripts/format-shell.sh",
                    "scripts/normalize-eof.sh",
                    "scripts/tracked.sh",
                },
            )


if __name__ == "__main__":
    unittest.main()
