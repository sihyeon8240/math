"""Integration tests for repository maintenance shell scripts."""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class CleanTests(unittest.TestCase):
    def test_clean_removes_make_and_vscode_build_contents(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(ROOT / "scripts/clean.sh", scripts / "clean.sh")
            (root / "build/nested").mkdir(parents=True)
            (root / "build/nested/output.pdf").write_bytes(b"pdf")
            (root / "vscode-build/nested").mkdir(parents=True)
            (root / "vscode-build/nested/output.pdf").write_bytes(b"pdf")
            outside = root / "keep.txt"
            outside.write_text("keep", encoding="utf-8")

            result = subprocess.run(
                [str(scripts / "clean.sh")],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(list((root / "build").iterdir()), [])
            self.assertEqual(list((root / "vscode-build").iterdir()), [])
            self.assertEqual(outside.read_text(encoding="utf-8"), "keep")


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
            latexmk.write_text(
                "#!/usr/bin/env bash\n"
                "set -euo pipefail\n"
                'printf "%s\\n" "$PWD" "$@" > "$LATEXMK_CAPTURE"\n',
                encoding="utf-8",
            )
            latexmk.chmod(0o755)
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


class CleanArtifactsTests(unittest.TestCase):
    def test_removes_artifacts_and_preserves_outputs_and_caches(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(
                ROOT / "scripts/clean-artifacts.sh",
                scripts / "clean-artifacts.sh",
            )

            artifacts = (
                root / "chapter.aux",
                root / "chapter.log",
                root / "change.patch.orig",
                root / "change.patch.rej",
                root / "notes.tex~",
                root / "notes.tex.bak",
                root / "notes.tex.swp",
                root / ".books.yml.interrupted.tmp",
            )
            for artifact in artifacts:
                artifact.write_text("discard", encoding="utf-8")

            preserved = (
                root / "tree.txt",
                root / "keep.tex",
                root / "build/book.log",
                root / "vscode-build/book.aux",
                root / ".latexindent_cache/indent.log",
                root / ".ruff_cache/state.log",
                root / "lean/.lake/build.log",
            )
            for path in preserved:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("keep", encoding="utf-8")

            result = subprocess.run(
                [str(scripts / "clean-artifacts.sh")],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(all(not artifact.exists() for artifact in artifacts))
            self.assertTrue(
                all(path.read_text(encoding="utf-8") == "keep" for path in preserved)
            )


class MakeBooksTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copy2(ROOT / "Makefile", self.root / "Makefile")
        shutil.copy2(ROOT / "scripts/check-log.py", scripts / "check-log.py")
        build = scripts / "build-book.sh"
        build.write_text(
            "#!/usr/bin/env bash\n"
            "set -euo pipefail\n"
            'mkdir -p "build/$1"\n'
            'printf %b "${BUILD_LOG_TEXT:-}" > "build/$1/book.log"\n',
            encoding="utf-8",
        )
        build.chmod(0o755)
        build_all = scripts / "build-all.sh"
        build_all.write_text(
            "#!/usr/bin/env bash\n"
            "set -euo pipefail\n"
            'printf %s "$*" > bulk-arguments\n'
            'printf %s "${CHECK_LOG_STRICT:-0}" > bulk-strict\n',
            encoding="utf-8",
        )
        build_all.chmod(0o755)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def run_make(
        self, *goals: str, log_text: str = ""
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["make", "books", "BOOK=sample", *goals],
            cwd=self.root,
            env={**os.environ, "PYTHON": sys.executable, "BUILD_LOG_TEXT": log_text},
            capture_output=True,
            text=True,
            check=False,
        )

    def test_check_rejects_a_latex_log_error(self) -> None:
        result = self.run_make(
            "check", log_text="LaTeX Warning: Reference `x` undefined.\n"
        )

        self.assertEqual(result.returncode, 2)
        self.assertIn("undefined reference", result.stderr)

    def test_strict_controls_overfull_box_failure(self) -> None:
        log = "Overfull \\hbox (1.0pt too wide) detected at line 1\n"

        advisory = self.run_make("check", log_text=log)
        strict = self.run_make("check", "strict", log_text=log)

        self.assertEqual(advisory.returncode, 0, advisory.stderr)
        self.assertIn("warning: overfull box", advisory.stderr)
        self.assertEqual(strict.returncode, 2)
        self.assertIn("error: overfull box", strict.stderr)

    def test_check_without_book_dispatches_to_bulk_validation(self) -> None:
        result = subprocess.run(
            ["make", "books", "check", "strict"],
            cwd=self.root,
            env={**os.environ, "PYTHON": sys.executable},
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((self.root / "bulk-arguments").read_text(), "check")
        self.assertEqual((self.root / "bulk-strict").read_text(), "1")

    def test_strict_requires_check(self) -> None:
        result = self.run_make("strict")

        self.assertEqual(result.returncode, 2)
        self.assertIn("strict requires check", result.stderr)


class MakeUsageTests(unittest.TestCase):
    def test_usage_lists_clean_forms_on_separate_lines(self) -> None:
        expected = [
            "usage: make clean {build|source}",
            "usage: make clean cache {lake|tex|ruff|py|all}",
        ]

        for goals in (("clean",), ("clean", "cache")):
            with self.subTest(goals=goals):
                result = subprocess.run(
                    ["make", *goals],
                    cwd=ROOT,
                    capture_output=True,
                    text=True,
                    check=False,
                )

                self.assertEqual(result.returncode, 2)
                self.assertEqual(result.stderr.splitlines()[:2], expected)

    def test_books_usage_matches_help_forms(self) -> None:
        result = subprocess.run(
            ["make", "books", "strict"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(result.returncode, 2)
        self.assertEqual(
            result.stderr.splitlines()[:3],
            [
                "error: strict requires check for a book build",
                "usage: make books [BOOK=<slug>]",
                "usage: make books [BOOK=<slug>] check [strict]",
            ],
        )

    def test_check_usage_matches_help_forms(self) -> None:
        result = subprocess.run(
            ["make", "check"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(result.returncode, 2)
        self.assertEqual(
            result.stderr.splitlines()[:2],
            [
                "usage: make check {manifest|source|proof-links}",
                "usage: make check all [strict]",
            ],
        )

    def test_doctor_usage_matches_help_forms(self) -> None:
        result = subprocess.run(
            ["make", "doctor"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(result.returncode, 2)
        self.assertEqual(
            result.stderr.splitlines()[:2],
            [
                "usage: make doctor env",
                "usage: make doctor books [BOOK=<slug>]",
            ],
        )


class FormatTexTests(unittest.TestCase):
    def test_only_tracked_tex_files_are_checked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(ROOT / "scripts/format-tex.sh", scripts / "format-tex.sh")
            shutil.copy2(
                ROOT / "scripts/normalize-eof.sh", scripts / "normalize-eof.sh"
            )
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            (root / "tracked.tex").write_text("tracked\n", encoding="utf-8")
            (root / "draft.tex").write_text("draft\n", encoding="utf-8")
            subprocess.run(["git", "add", "tracked.tex"], cwd=root, check=True)

            binary = root / "bin"
            binary.mkdir()
            latexindent = binary / "latexindent"
            latexindent.write_text(
                "#!/usr/bin/env python3\n"
                "import os, pathlib, sys\n"
                'if "--version" in sys.argv:\n'
                '    print("latexindent fake")\n'
                "    raise SystemExit(0)\n"
                'capture = pathlib.Path(os.environ["FORMAT_TEX_CAPTURE"])\n'
                'with capture.open("a", encoding="utf-8") as stream:\n'
                "    for argument in sys.argv[1:]:\n"
                '        if argument.endswith((".tex", ".sty")):\n'
                '            stream.write(argument + "\\n")\n',
                encoding="utf-8",
            )
            latexindent.chmod(0o755)
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
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(
                capture.read_text(encoding="utf-8").splitlines(), ["tracked.tex"]
            )


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
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            (scripts / "tracked.sh").write_text(
                "#!/usr/bin/env bash\n", encoding="utf-8"
            )
            (scripts / "draft.sh").write_text("#!/usr/bin/env bash\n", encoding="utf-8")
            (root / "outside.sh").write_text("#!/usr/bin/env bash\n", encoding="utf-8")
            subprocess.run(["git", "add", "scripts/tracked.sh"], cwd=root, check=True)

            binary = root / "bin"
            binary.mkdir()
            shfmt = binary / "shfmt"
            shfmt.write_text(
                "#!/usr/bin/env python3\n"
                "import os, pathlib, sys\n"
                'capture = pathlib.Path(os.environ["FORMAT_SHELL_CAPTURE"])\n'
                'with capture.open("w", encoding="utf-8") as stream:\n'
                "    for argument in sys.argv[1:]:\n"
                '        if argument.endswith(".sh"):\n'
                '            stream.write(argument + "\\n")\n',
                encoding="utf-8",
            )
            shfmt.chmod(0o755)
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


class NormalizeEofTests(unittest.TestCase):
    def test_format_condenses_consecutive_blank_lines_when_requested(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "multiple-blank-lines.tex"
            path.write_bytes(b"first\n\n\nsecond\n")

            result = subprocess.run(
                [
                    str(ROOT / "scripts/normalize-eof.sh"),
                    "--collapse-blank-lines",
                    str(path),
                ],
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(path.read_bytes(), b"first\n\nsecond\n")

    def test_format_adds_one_lf_and_removes_trailing_blank_lines(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            paths = [
                Path(directory) / "missing-newline.tex",
                Path(directory) / "trailing-blank-lines.tex",
            ]
            paths[0].write_bytes(b"content")
            paths[1].write_bytes(b"content\n\n\n")

            result = subprocess.run(
                [str(ROOT / "scripts/normalize-eof.sh"), *map(str, paths)],
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertTrue(all(path.read_bytes() == b"content\n" for path in paths))

    def test_check_rejects_missing_or_extra_final_lf(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            valid = Path(directory) / "valid.tex"
            missing = Path(directory) / "missing.tex"
            extra = Path(directory) / "extra.tex"
            valid.write_bytes(b"content\n")
            missing.write_bytes(b"content")
            extra.write_bytes(b"content\n\n")

            valid_result = subprocess.run(
                [str(ROOT / "scripts/normalize-eof.sh"), "--check", str(valid)],
                capture_output=True,
                text=True,
                check=False,
            )
            invalid_result = subprocess.run(
                [
                    str(ROOT / "scripts/normalize-eof.sh"),
                    "--check",
                    str(missing),
                    str(extra),
                ],
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(valid_result.returncode, 0, valid_result.stderr)
            self.assertEqual(invalid_result.returncode, 1)
            self.assertIn(str(missing), invalid_result.stderr)
            self.assertIn(str(extra), invalid_result.stderr)

    def test_without_paths_processes_tracked_text_only(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            tracked = root / "tracked.txt"
            untracked = root / "untracked.txt"
            binary = root / "binary.dat"
            tracked.write_bytes(b"tracked")
            untracked.write_bytes(b"untracked")
            binary.write_bytes(b"binary\0data")
            subprocess.run(
                ["git", "add", "tracked.txt", "binary.dat"], cwd=root, check=True
            )

            result = subprocess.run(
                [str(ROOT / "scripts/normalize-eof.sh")],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(tracked.read_bytes(), b"tracked\n")
            self.assertEqual(untracked.read_bytes(), b"untracked")
            self.assertEqual(binary.read_bytes(), b"binary\0data")


class BuildBookTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
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
        (binary / "latexmk").write_text(
            textwrap.dedent("""\
            #!/usr/bin/env bash
            set -euo pipefail
            printf '%s\n' "$TEXINPUTS" > "$LATEXMK_CAPTURE/texinputs"
            printf '%s\n' "$@" > "$LATEXMK_CAPTURE/arguments"
            if [[ -e "$LATEXMK_CAPTURE/book.pdf" ]]; then touch "$LATEXMK_CAPTURE/stale-pdf-observed"; fi
            touch "$LATEXMK_CAPTURE/book.pdf"
            """),
            encoding="utf-8",
        )
        (binary / "latexmk").chmod(0o755)
        self.path = f"{binary}:{os.environ['PATH']}"

    def tearDown(self) -> None:
        self.temporary.cleanup()

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
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((output / "chapters/01-start").is_dir())
        self.assertIn(
            str(self.root / "common/styles//"), (output / "texinputs").read_text()
        )
        self.assertIn(f"-outdir={output}", (output / "arguments").read_text())

    def test_removes_stale_pdf_before_latexmk(self) -> None:
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
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse((output / "stale-pdf-observed").exists())
        self.assertTrue((output / "book.pdf").exists())

    def test_missing_entry_point_is_rejected_before_latexmk(self) -> None:
        (self.root / "books/sample/book.tex").unlink()
        result = subprocess.run(
            [str(self.root / "scripts/build-book.sh"), "sample"],
            cwd=self.root,
            env={**os.environ, "PATH": self.path, "PYTHON": sys.executable},
            capture_output=True,
            text=True,
            check=False,
        )

        self.assertEqual(result.returncode, 2)
        self.assertIn("missing its entry point", result.stderr)


class EnvironmentCheckTests(unittest.TestCase):
    def test_missing_repository_structure_is_reported_after_toolchain_check(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(ROOT / "scripts/check-environment.sh", scripts)
            (scripts / "check-toolchain.sh").write_text(
                "#!/usr/bin/env bash\nexit 0\n", encoding="utf-8"
            )
            (scripts / "check-toolchain.sh").chmod(0o755)

            result = subprocess.run(
                [str(scripts / "check-environment.sh")],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
            )

            self.assertEqual(result.returncode, 1)
            self.assertIn("Makefile missing", result.stderr)


class NewBookTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        scripts = self.root / "scripts"
        templates = self.root / "common/templates"
        scripts.mkdir(parents=True)
        templates.mkdir(parents=True)
        (self.root / "books").mkdir()
        (self.root / "books.yml").write_text("books: []\n", encoding="utf-8")
        shutil.copy2(ROOT / "scripts/new-book.sh", scripts / "new-book.sh")
        for name, content in {
            "book.tex": "book\n",
            "chapter.tex": "chapter xx:ch:start\n",
            "section.tex": "section xx:sec:first\n",
            "chapters.yml": "chapters\n",
            "sections.yml": "sections\n",
            "references.bib": "",
        }.items():
            (templates / name).write_text(content, encoding="utf-8")
        (scripts / "books.py").write_text(
            textwrap.dedent("""\
            import os
            import sys
            if sys.argv[1] == "add" and os.environ.get("FAIL_ADD") == "1":
                raise SystemExit(1)
            if sys.argv[1] == "label-prefix":
                print("nb")
            """),
            encoding="utf-8",
        )
        (scripts / "generate-contents.py").write_text("", encoding="utf-8")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def run_new(
        self, slug: str = "new-book", **environment: str
    ) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(self.root / "scripts/new-book.sh"), slug, "New Book"],
            cwd=self.root,
            env={**os.environ, "PYTHON": sys.executable, **environment},
            capture_output=True,
            text=True,
            check=False,
        )

    def test_success_creates_minimal_scaffold(self) -> None:
        result = self.run_new()
        target = self.root / "books/new-book"
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue((target / "chapters/01-introduction/index.tex").is_file())
        self.assertFalse((target / "frontmatter").exists())
        self.assertFalse((target / "metadata.tex").exists())
        self.assertFalse((target / "local-style.sty").exists())
        self.assertTrue((target / "references.bib").is_file())
        self.assertIn(
            "nb:sec:first",
            (target / "chapters/01-introduction/01-first-section.tex").read_text(),
        )
        self.assertFalse((target / "README.md").exists())

    def test_existing_target_is_preserved(self) -> None:
        target = self.root / "books/new-book"
        target.mkdir()
        marker = target / "keep"
        marker.write_text("keep", encoding="utf-8")
        result = self.run_new()
        self.assertEqual(result.returncode, 1)
        self.assertTrue(marker.is_file())

    def test_failure_after_creation_removes_partial_scaffold(self) -> None:
        result = self.run_new(FAIL_ADD="1")
        self.assertEqual(result.returncode, 1)
        self.assertFalse((self.root / "books/new-book").exists())
        self.assertIn("creation failed", result.stderr)


if __name__ == "__main__":
    unittest.main()
