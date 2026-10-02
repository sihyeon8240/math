"""Repository source checks and end-of-file normalization."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from test_support import write_executable

ROOT = Path(__file__).resolve().parent.parent


class RepositorySourceCheckTests(unittest.TestCase):
    def test_syntax_error_in_later_script_stops_source_checks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            scripts = root / "scripts"
            scripts.mkdir()
            shutil.copy2(ROOT / "scripts/check-repository.sh", scripts)
            (scripts / "aaa-valid.sh").write_text("exit 0\n", encoding="utf-8")
            (scripts / "zzz-invalid.sh").write_text("if then\n", encoding="utf-8")
            binary = root / "bin"
            binary.mkdir()
            # Syntax checking must reject the script independently of ShellCheck.
            for name in ("rg", "shellcheck"):
                command = binary / name
                write_executable(command, "#!/bin/sh\nexit 0\n")
            result = subprocess.run(
                [str(scripts / "check-repository.sh")],
                cwd=root,
                env={**os.environ, "PATH": f"{binary}:{os.environ['PATH']}"},
                capture_output=True,
                text=True,
                check=False,
                timeout=10,
            )
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("zzz-invalid.sh", result.stderr)
            self.assertIn("syntax error", result.stderr)
            self.assertNotIn("books.py", result.stderr)


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
                timeout=30,
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
                timeout=30,
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
                timeout=30,
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
                timeout=30,
            )

            self.assertEqual(valid_result.returncode, 0, valid_result.stderr)
            self.assertEqual(invalid_result.returncode, 1)
            self.assertIn(str(missing), invalid_result.stderr)
            self.assertIn(str(extra), invalid_result.stderr)

    def test_full_check_excludes_only_paths_covered_by_formatters(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, timeout=30)
            covered = [
                "scripts/helper.py",
                "tests/test_sample.py",
                "scripts/build.sh",
                "books/sample/book.tex",
                "common/styles/sample.sty",
            ]
            remaining = ["README.md", "lean/Sample.lean", "other/helper.py"]
            for name in covered + remaining:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(b"missing newline")
            subprocess.run(["git", "add", "."], cwd=root, check=True, timeout=30)

            command = [str(ROOT / "scripts/normalize-eof.sh"), "--check"]
            result = subprocess.run(
                [*command, "--exclude-formatted"],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )
            self.assertEqual(result.returncode, 1)
            for name in covered:
                self.assertNotIn(name, result.stderr)
            for name in remaining:
                self.assertIn(name, result.stderr)

            standalone = subprocess.run(
                command,
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )
            self.assertEqual(standalone.returncode, 1)
            for name in covered + remaining:
                self.assertIn(name, standalone.stderr)

    def test_without_paths_processes_tracked_text_only(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True, timeout=30)
            tracked = root / "tracked.txt"
            untracked = root / "untracked.txt"
            binary = root / "binary.dat"
            tracked.write_bytes(b"tracked")
            untracked.write_bytes(b"untracked")
            binary.write_bytes(b"binary\0data")
            subprocess.run(
                ["git", "add", "tracked.txt", "binary.dat"],
                cwd=root,
                check=True,
                timeout=30,
            )

            result = subprocess.run(
                [str(ROOT / "scripts/normalize-eof.sh")],
                cwd=root,
                capture_output=True,
                text=True,
                check=False,
                timeout=30,
            )

            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(tracked.read_bytes(), b"tracked\n")
            self.assertEqual(untracked.read_bytes(), b"untracked")
            self.assertEqual(binary.read_bytes(), b"binary\0data")


if __name__ == "__main__":
    unittest.main()
