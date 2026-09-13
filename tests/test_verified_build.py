"""Regression tests for validated PR PDF reuse and cache boundaries."""

from __future__ import annotations

import importlib.util
import io
import json
import os
import subprocess
import tempfile
import unittest
import zipfile
from pathlib import Path
from unittest.mock import patch

import yaml

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "verified_build", ROOT / "scripts/verified-build.py"
)
assert SPEC and SPEC.loader
BUILD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILD)


class VerifiedBuildTests(unittest.TestCase):
    def setUp(self):
        self.expected = {
            "policy": BUILD.POLICY,
            "book": "linear-algebra",
            "image": "ghcr.io/example/math@sha256:" + "a" * 64,
            "platform": "linux/amd64",
            "tree": "b" * 40,
        }
        self.run = {
            "id": 123,
            "run_attempt": 2,
            "event": "pull_request",
            "status": "completed",
            "conclusion": "success",
            "head_sha": "c" * 40,
            "head_repository": {"full_name": "example/math"},
            "path": ".github/workflows/build.yml",
        }
        self.files = {"book.pdf": b"%PDF-1.5\nverified", "book.log": b"clean log\n"}

    def archive(self, *, identity=None, files=None, extra=None, manifest_update=None):
        files = self.files if files is None else files
        manifest = {
            **(self.expected if identity is None else identity),
            "run_id": "123",
            "run_attempt": "2",
            "checksums": {name: BUILD.checksum(data) for name, data in files.items()},
            **(manifest_update or {}),
        }
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, "w") as archive:
            for name, data in {**files, **(extra or {})}.items():
                archive.writestr(name, data)
            archive.writestr("verified-build.json", json.dumps(manifest))
        return stream.getvalue()

    def test_matching_verified_archive_is_accepted(self):
        self.assertEqual(
            BUILD.verify_archive(self.archive(), self.expected, self.run), self.files
        )

    def test_every_build_identity_field_must_match(self):
        for key in self.expected:
            with self.subTest(key=key):
                changed = {**self.expected, key: "changed"}
                with self.assertRaisesRegex(ValueError, "identity differs"):
                    BUILD.verify_archive(
                        self.archive(identity=changed), self.expected, self.run
                    )

    def test_run_and_attempt_must_match(self):
        for key in ("run_id", "run_attempt"):
            with (
                self.subTest(key=key),
                self.assertRaisesRegex(ValueError, "different run"),
            ):
                BUILD.verify_archive(
                    self.archive(manifest_update={key: "999"}), self.expected, self.run
                )

    def test_file_checksums_are_checked(self):
        with self.assertRaisesRegex(ValueError, "checksum"):
            BUILD.verify_archive(
                self.archive(manifest_update={"checksums": {}}), self.expected, self.run
            )

    def test_unexpected_paths_and_missing_files_are_rejected(self):
        for data in (
            self.archive(extra={"../../outside": b"bad"}),
            self.archive(files={"book.pdf": self.files["book.pdf"]}),
        ):
            with self.assertRaisesRegex(ValueError, "unexpected artifact files"):
                BUILD.verify_archive(data, self.expected, self.run)

    def test_empty_log_and_non_pdf_are_rejected(self):
        for files in (
            {**self.files, "book.log": b""},
            {**self.files, "book.pdf": b"not PDF"},
        ):
            with self.assertRaises(ValueError):
                BUILD.verify_archive(self.archive(files=files), self.expected, self.run)

    def test_artifact_size_limit(self):
        with patch.object(BUILD, "MAX_BYTES", 1), self.assertRaises(ValueError):
            BUILD.verify_archive(self.archive(), self.expected, self.run)

    def test_only_successful_same_repository_pr_runs_are_eligible(self):
        self.assertTrue(BUILD.eligible_run(self.run, "example/math", "c" * 40))
        for field, value in (
            ("event", "push"),
            ("status", "in_progress"),
            ("conclusion", "failure"),
            ("head_sha", "d" * 40),
            ("path", ".github/workflows/other.yml"),
            ("head_repository", {"full_name": "fork/math"}),
        ):
            with self.subTest(field=field):
                self.assertFalse(
                    BUILD.eligible_run(
                        {**self.run, field: value}, "example/math", "c" * 40
                    )
                )

    def restore(
        self,
        *,
        pull_update=None,
        artifact_update=None,
        archive=None,
        run_update=None,
        log_fails=False,
    ):
        data = archive if archive is not None else self.archive()
        pull = {
            "number": 42,
            "merged_at": "2026-09-07",
            "merge_commit_sha": "d" * 40,
            "base": {"ref": "main"},
            "head": {"sha": "c" * 40, "repo": {"full_name": "example/math"}},
            **(pull_update or {}),
        }
        artifact = {
            "id": 789,
            "name": "linear-algebra-verified-build",
            "expired": False,
            "size_in_bytes": len(data),
            "digest": "sha256:" + BUILD.checksum(data),
            **(artifact_update or {}),
        }
        responses = [
            [pull],
            {"workflow_runs": [{**self.run, **(run_update or {})}]},
            {"artifacts": [artifact]},
        ]

        def command(*args):
            if args[0] == "gh":
                return data
            if log_fails:
                raise subprocess.CalledProcessError(1, args)
            return b""

        with (
            tempfile.TemporaryDirectory() as temporary,
            patch.dict(
                os.environ,
                {
                    "GITHUB_REPOSITORY": "example/math",
                    "GITHUB_SHA": "d" * 40,
                },
            ),
            patch.object(BUILD, "api", side_effect=responses) as api,
            patch.object(BUILD, "command", side_effect=command) as cmd,
        ):
            directory = Path(temporary)
            reused = BUILD.restore(self.expected, directory)
            pdf = (
                (directory / "book.pdf").read_bytes()
                if (directory / "book.pdf").exists()
                else None
            )
            return reused, pdf, api.call_count, cmd.call_args_list

    def test_restore_downloads_and_rechecks_matching_pdf(self):
        reused, pdf, calls, commands = self.restore()
        self.assertTrue(reused)
        self.assertEqual(pdf, self.files["book.pdf"])
        self.assertEqual(calls, 3)
        self.assertIn("--strict", commands[-1].args)

    def test_unmerged_unrelated_and_fork_prs_never_download(self):
        for change in (
            {"merged_at": None},
            {"merge_commit_sha": "e" * 40},
            {"base": {"ref": "other"}},
            {"head": {"repo": {"full_name": "fork/math"}}},
            {"head": {"repo": None}},
        ):
            with self.subTest(change=change):
                reused, pdf, calls, commands = self.restore(pull_update=change)
                self.assertFalse(reused)
                self.assertIsNone(pdf)
                self.assertEqual(calls, 1)
                self.assertEqual(commands, [])

    def test_missing_expired_or_wrong_artifacts_fall_back(self):
        for change in (
            {"expired": True},
            {"name": "other-book-verified-build"},
            {"size_in_bytes": BUILD.MAX_BYTES + 1},
            {"digest": "sha256:wrong"},
        ):
            with self.subTest(change=change):
                self.assertFalse(self.restore(artifact_update=change)[0])

    def test_failed_run_invalid_archive_and_bad_log_fall_back(self):
        self.assertFalse(self.restore(run_update={"conclusion": "failure"})[0])
        self.assertFalse(self.restore(archive=b"not zip")[0])
        self.assertFalse(self.restore(log_fails=True)[0])

    def test_changed_source_tree_falls_back(self):
        changed = {**self.expected, "tree": "e" * 40}
        self.assertFalse(self.restore(archive=self.archive(identity=changed))[0])

    def test_lookup_failure_emits_rebuild_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary) / "output"
            with (
                patch.dict(os.environ, {"GITHUB_OUTPUT": str(output)}),
                patch(
                    "sys.argv",
                    [
                        "verified-build.py",
                        "restore",
                        "--book",
                        "linear-algebra",
                        "--image",
                        self.expected["image"],
                    ],
                ),
                patch.object(BUILD, "identity", return_value=self.expected),
                patch.object(
                    BUILD, "restore", side_effect=subprocess.CalledProcessError(1, "gh")
                ),
            ):
                BUILD.main()
            self.assertEqual(output.read_text(), "reused=false\n")

    def test_record_requires_strict_log_check(self):
        with (
            tempfile.TemporaryDirectory() as temporary,
            patch.object(
                BUILD,
                "command",
                side_effect=subprocess.CalledProcessError(1, "check-log"),
            ),
        ):
            with self.assertRaises(subprocess.CalledProcessError):
                BUILD.record(self.expected, Path(temporary))
            self.assertFalse((Path(temporary) / "verified-build.json").exists())

    def test_record_round_trip(self):
        with (
            tempfile.TemporaryDirectory() as temporary,
            patch.dict(
                os.environ,
                {
                    "GITHUB_RUN_ID": "123",
                    "GITHUB_RUN_ATTEMPT": "2",
                },
            ),
            patch.object(BUILD, "command", return_value=b""),
        ):
            directory = Path(temporary)
            for name, data in self.files.items():
                (directory / name).write_bytes(data)
            BUILD.record(self.expected, directory)
            manifest = json.loads((directory / "verified-build.json").read_text())
            self.assertEqual(manifest["tree"], self.expected["tree"])
            self.assertEqual(
                manifest["checksums"]["book.pdf"],
                BUILD.checksum(self.files["book.pdf"]),
            )

    def test_ci_has_one_image_preparation_and_preserves_required_check_names(self):
        workflow = yaml.safe_load((ROOT / ".github/workflows/build.yml").read_text())
        jobs = workflow["jobs"]
        self.assertEqual(
            sum(
                job.get("uses", "").endswith("/prepare-image.yml")
                for job in jobs.values()
            ),
            1,
        )
        self.assertFalse((ROOT / ".github/workflows/check.yml").exists())
        self.assertEqual(jobs["check"]["name"], "Check sources")
        self.assertEqual(jobs["build-check"]["name"], "Verify textbook builds")
        self.assertNotIn("needs", jobs["source"])
        self.assertNotIn("needs", jobs["plan"])

    def test_cache_boundaries_and_reuse_build_fallback(self):
        jobs = yaml.safe_load((ROOT / ".github/workflows/build.yml").read_text())[
            "jobs"
        ]
        lean_cache = next(
            step
            for step in jobs["source"]["steps"]
            if step.get("name") == "Cache Lean dependencies and build outputs"
        )
        for filename in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            self.assertIn(filename, lean_cache["with"]["restore-keys"])
        steps = jobs["book"]["steps"]
        cache = next(
            step for step in steps if step.get("name") == "Cache LaTeX build outputs"
        )
        self.assertIn("steps.inputs.outputs.image", cache["with"]["restore-keys"])
        self.assertIn("matrix.book", cache["with"]["restore-keys"])
        self.assertIn("steps.inputs.outputs.tree", cache["with"]["key"])
        build = next(
            step
            for step in steps
            if step.get("name") == "Build and strictly check in the prepared image"
        )
        self.assertEqual(build["if"], "steps.reuse.outputs.reused != 'true'")
        self.assertNotIn("cache-hit", build["if"])
        reuse = next(step for step in steps if step.get("id") == "reuse")
        self.assertEqual(reuse["if"], "github.event_name == 'push'")


if __name__ == "__main__":
    unittest.main()
