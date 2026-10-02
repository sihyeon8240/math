"""Build orchestration and public Make build commands."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

from test_support import write_executable

ROOT = Path(__file__).resolve().parent.parent


class FullCheckTests(unittest.TestCase):
    def test_full_check_defers_links_and_stops_on_lean_failure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(ROOT / "scripts/check.sh", scripts)
            names = [
                "check-repository.sh",
                "format-python.sh",
                "format-shell.sh",
                "format-tex.sh",
                "normalize-eof.sh",
                "check-lean.sh",
                "build-all.sh",
            ]
            for name in names:
                script = scripts / name
                write_executable(
                    script,
                    "#!/bin/sh\n"
                    'printf "%s %s\\n" "${0##*/}" "$*" >> "$CAPTURE"\n'
                    + (
                        'exit "${LEAN_EXIT_CODE:-0}"\n'
                        if name == "check-lean.sh"
                        else ""
                    ),
                )

            for status in (0, 7):
                with self.subTest(status=status):
                    capture = root / f"calls-{status}"
                    result = subprocess.run(
                        [str(scripts / "check.sh")],
                        cwd=root,
                        env={
                            **os.environ,
                            "CAPTURE": str(capture),
                            "LEAN_EXIT_CODE": str(status),
                        },
                        capture_output=True,
                        text=True,
                        check=False,
                        timeout=30,
                    )
                    self.assertEqual(result.returncode, status, result.stderr)
                    calls = capture.read_text().splitlines()
                    self.assertEqual(calls[0], "check-repository.sh --defer-lean")
                    self.assertIn("normalize-eof.sh --check --exclude-formatted", calls)
                    self.assertEqual(calls.count("check-lean.sh "), 1)
                    self.assertEqual("build-all.sh check" in calls, status == 0)


class BuildVSCodeTests(unittest.TestCase):
    def test_prepares_output_tree_before_running_latexmk(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(
                ROOT / "scripts/build-vscode.sh",
                scripts / "build-vscode.sh",
            )
            (root / "latexmkrc").write_text("", encoding="utf-8")
            book = root / "books/example"
            (book / "chapters/01-example").mkdir(parents=True)
            document = book / "book.tex"
            document.write_text("", encoding="utf-8")
            output = root / "vscode-build/books/example"

            bin_dir = root / "bin"
            bin_dir.mkdir()
            latexmk = bin_dir / "latexmk"
            write_executable(
                latexmk,
                "#!/usr/bin/env bash\n"
                "set -euo pipefail\n"
                'printf "%s\\n" "$PWD" "$@" > "$LATEXMK_CAPTURE"\n',
            )
            capture = root / "latexmk-arguments"
            environment = os.environ.copy()
            environment["PATH"] = f"{bin_dir}:{environment['PATH']}"
            environment["LATEXMK_CAPTURE"] = str(capture)

            result = subprocess.run(
                [
                    str(scripts / "build-vscode.sh"),
                    str(output),
                    str(document),
                    "-shell-escape",
                ],
                cwd=root,
                env=environment,
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue((output / "chapters/01-example").is_dir())
            self.assertEqual(
                capture.read_text(encoding="utf-8").splitlines(),
                [
                    str(book),
                    "-r",
                    str(root / "latexmkrc"),
                    f"-outdir={output}",
                    "-shell-escape",
                    "book.tex",
                ],
            )


class MakeBooksTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copy2(ROOT / "Makefile", self.root / "Makefile")
        shutil.copy2(ROOT / "scripts/check-log.py", scripts / "check-log.py")
        build = scripts / "build-book.sh"
        write_executable(
            build,
            "#!/usr/bin/env bash\n"
            "set -euo pipefail\n"
            'mkdir -p "build/$1"\n'
            'printf %b "${BUILD_LOG_TEXT:-}" > "build/$1/book.log"\n',
        )
        build_all = scripts / "build-all.sh"
        write_executable(
            build_all,
            "#!/usr/bin/env bash\n"
            "set -euo pipefail\n"
            'printf %s "$*" > bulk-arguments\n'
            'printf %s "${CHECK_LOG_STRICT:-0}" > bulk-strict\n',
        )

    def run_make(
        self, *goals: str, log_text: str = ""
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["make", "book", "BOOK=sample", *goals],
            cwd=self.root,
            env={**os.environ, "PYTHON": sys.executable, "BUILD_LOG_TEXT": log_text},
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )

    def test_check_rejects_a_latex_log_error(self) -> None:
        result = self.run_make(
            "check", log_text="LaTeX Warning: Reference `x` undefined.\n"
        )

        self.assertEqual(result.returncode, 2)
        self.assertIn("undefined reference", result.stderr)

    def test_build_failure_is_not_masked_by_a_previous_clean_log(self) -> None:
        output = self.root / "build/sample"
        output.mkdir(parents=True)
        (output / "book.log").write_text("Previous successful build\n")
        (self.root / "scripts/build-book.sh").write_text(
            "#!/usr/bin/env bash\necho build-failed >&2\nexit 23\n"
        )
        for goals in ((), ("check",), ("check", "strict")):
            with self.subTest(goals=goals):
                result = self.run_make(*goals)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("build-failed", result.stderr)

    def test_strict_controls_overfull_box_failure(self) -> None:
        log = (
            "Overfull \\hbox (1.0pt too wide) detected at line 1\n"
            "Output written on book.pdf (1 page, 123 bytes).\n"
        )

        advisory = self.run_make("check", log_text=log)
        strict = self.run_make("check", "strict", log_text=log)

        self.assertEqual(advisory.returncode, 0, advisory.stderr)
        self.assertIn("warning: overfull box", advisory.stderr)
        self.assertEqual(strict.returncode, 2)
        self.assertIn("error: overfull box", strict.stderr)

    def test_check_without_book_dispatches_to_bulk_validation(self) -> None:
        result = subprocess.run(
            ["make", "book", "check", "strict"],
            cwd=self.root,
            env={**os.environ, "PYTHON": sys.executable},
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.root / "bulk-arguments").read_text(), "check")
        self.assertEqual((self.root / "bulk-strict").read_text(), "1")

    def test_strict_requires_check(self) -> None:
        result = self.run_make("strict")

        self.assertEqual(result.returncode, 2)
        self.assertIn("strict requires check", result.stderr)


class BuildBookTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copy2(ROOT / "scripts/build-book.sh", scripts / "build-book.sh")
        (scripts / "books.py").write_text(
            textwrap.dedent("""\
            import sys
            if sys.argv[1:3] != ["require", "sample"]:
                raise SystemExit(1)
            """),
            encoding="utf-8",
        )
        (self.root / "latexmkrc").write_text("", encoding="utf-8")
        (self.root / "common/styles").mkdir(parents=True)
        (self.root / "common/templates").mkdir(parents=True)
        book = self.root / "books/sample"
        (book / "chapters/01-start").mkdir(parents=True)
        (book / "book.tex").write_text("book", encoding="utf-8")
        binary = self.root / "bin"
        binary.mkdir()
        write_executable(
            binary / "latexmk",
            textwrap.dedent("""\
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$TEXINPUTS" > "$LATEXMK_CAPTURE/texinputs"
            printf '%s\n' "$@" > "$LATEXMK_CAPTURE/arguments"
            if [[ -e "$LATEXMK_CAPTURE/book.pdf" ]]; then
              touch "$LATEXMK_CAPTURE/stale-pdf-observed"
            fi
            touch "$LATEXMK_CAPTURE/book.pdf"
            exit "${LATEXMK_EXIT_CODE:-0}"
            """),
        )
        self.path = f"{binary}:{os.environ['PATH']}"

    def test_build_creates_mirrored_output_and_passes_texinputs(self) -> None:
        output = self.root / "build/sample"
        result = subprocess.run(
            [str(self.root / "scripts/build-book.sh"), "sample"],
            cwd=self.root,
            env={
                **os.environ,
                "PATH": self.path,
                "PYTHON": sys.executable,
                "LATEXMK_CAPTURE": str(output),
            },
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((output / "chapters/01-start").is_dir())
        self.assertIn(
            str(self.root / "common/styles//"), (output / "texinputs").read_text()
        )
        self.assertIn(f"-outdir={output}", (output / "arguments").read_text())

    def test_preserves_pdf_for_incremental_latexmk(self) -> None:
        output = self.root / "build/sample"
        output.mkdir(parents=True)
        (output / "book.pdf").write_text("stale", encoding="utf-8")

        result = subprocess.run(
            [str(self.root / "scripts/build-book.sh"), "sample"],
            cwd=self.root,
            env={
                **os.environ,
                "PATH": self.path,
                "PYTHON": sys.executable,
                "LATEXMK_CAPTURE": str(output),
            },
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((output / "stale-pdf-observed").exists())
        self.assertTrue((output / "book.pdf").exists())

    def test_failed_latexmk_removes_pdf_and_preserves_exit_status(self) -> None:
        output = self.root / "build/sample"
        output.mkdir(parents=True)
        (output / "book.pdf").write_text("stale", encoding="utf-8")

        result = subprocess.run(
            [str(self.root / "scripts/build-book.sh"), "sample"],
            cwd=self.root,
            env={
                **os.environ,
                "PATH": self.path,
                "PYTHON": sys.executable,
                "LATEXMK_CAPTURE": str(output),
                "LATEXMK_EXIT_CODE": "17",
            },
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )

        self.assertEqual(result.returncode, 17, result.stderr)
        self.assertFalse((output / "book.pdf").exists())
        self.assertNotIn("==> Built", result.stdout)

    def test_missing_entry_point_is_rejected_before_latexmk(self) -> None:
        (self.root / "books/sample/book.tex").unlink()
        result = subprocess.run(
            [str(self.root / "scripts/build-book.sh"), "sample"],
            cwd=self.root,
            env={**os.environ, "PATH": self.path, "PYTHON": sys.executable},
            capture_output=True,
            text=True,
            check=False,
            timeout=30,
        )

        self.assertEqual(result.returncode, 2)
        self.assertIn("missing its entry point", result.stderr)


if __name__ == "__main__":
    unittest.main()
