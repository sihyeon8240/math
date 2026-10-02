"""Regression tests for workflow shell helpers and inline run blocks."""

from __future__ import annotations

import itertools
import json
import os
import re
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml

ROOT = Path(__file__).resolve().parent.parent


class WorkflowShellTests(unittest.TestCase):
    @staticmethod
    def build_workflow():
        return yaml.safe_load(
            (ROOT / ".github/workflows/build.yml").read_text(encoding="utf-8")
        )

    def test_configuration_shell_helpers_parse(self):
        for relative in (
            "scripts/open-image-pin-pr.sh",
            "scripts/check-image-tag.sh",
            "scripts/check-toolchain.sh",
            "scripts/export-config.sh",
        ):
            with self.subTest(relative=relative):
                result = subprocess.run(
                    ["bash", "-n", ROOT / relative],
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertEqual(result.returncode, 0, result.stderr)

    def run_pdf_update(
        self,
        updated: dict[str, bytes],
        existing: dict[str, bytes],
        *,
        registered=("alpha", "beta"),
        site=("alpha", "beta"),
    ):
        workflow = self.build_workflow()
        publish = next(
            step["run"]
            for step in workflow["jobs"]["publish"]["steps"]
            if step.get("id") == "publish"
        )
        start = publish.index("mkdir -p snapshot/pdf")
        end = publish.index("printf '%s\\n' \"$GITHUB_SHA\"")
        script = "set -euo pipefail\n" + publish[start:end]

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "snapshot" / "pdf").mkdir(parents=True)
            for name, data in existing.items():
                (root / "snapshot" / "pdf" / name).write_bytes(data)
            if updated:
                (root / "updated-pdfs").mkdir()
                for name, data in updated.items():
                    (root / "updated-pdfs" / name).write_bytes(data)
            (root / "scripts").mkdir()
            (root / "scripts" / "books.py").write_text(
                """#!/usr/bin/env python3
import json
import os
import sys
registered = os.environ["REGISTERED"].split()
site = os.environ["SITE"].split()
if sys.argv[1] == "require":
    with open(os.environ["REQUIRE_LOG"], "a", encoding="utf-8") as log:
        log.write(sys.argv[2] + "\\n")
    raise SystemExit(0 if sys.argv[2] in registered else 1)
if sys.argv[1:] == ["list", "--for", "site"]:
    print(*site, sep="\\n")
    raise SystemExit(0)
raise SystemExit(2)
""",
                encoding="utf-8",
            )
            require_log = root / "require.log"
            result = subprocess.run(
                ["bash", "-c", script],
                cwd=root,
                text=True,
                capture_output=True,
                check=False,
                env={
                    **os.environ,
                    "REGISTERED": " ".join(registered),
                    "SITE": " ".join(site),
                    "REQUIRE_LOG": str(require_log),
                },
            )
            snapshot = {
                path.name: path.read_bytes()
                for path in (root / "snapshot" / "pdf").iterdir()
            }
            required = (
                require_log.read_text(encoding="utf-8").splitlines()
                if require_log.exists()
                else []
            )
            return result, snapshot, required

    def run_snapshot(self, **values: str):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            output = root / "output"
            git = root / "git"
            git.write_text(
                """#!/usr/bin/env bash
case "$1" in
  fetch) exit "${FETCH_STATUS:-0}" ;;
  show) printf '%s' "${SOURCE_SHA:-}"; exit "${SHOW_STATUS:-0}" ;;
  cat-file) exit "${COMMIT_STATUS:-0}" ;;
  merge-base) exit "${ANCESTOR_STATUS:-0}" ;;
  *) exit 2 ;;
esac
""",
                encoding="utf-8",
            )
            git.chmod(0o755)
            env = {
                **os.environ,
                **values,
                "GITHUB_OUTPUT": str(output),
                "PATH": f"{root}:{os.environ['PATH']}",
            }
            result = subprocess.run(
                [ROOT / "scripts/snapshot-base.sh"],
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            return result, output.read_text(encoding="utf-8")

    def test_snapshot_base_valid_sha(self):
        sha = "a" * 40
        result, output = self.run_snapshot(SOURCE_SHA=sha)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, f"base={sha}\n")

    def test_snapshot_base_failures_emit_explicit_empty_base(self):
        cases = (
            {"FETCH_STATUS": "1"},
            {"SHOW_STATUS": "1"},
            {"SOURCE_SHA": "invalid"},
            {"SOURCE_SHA": "a" * 40, "COMMIT_STATUS": "1"},
            {"SOURCE_SHA": "a" * 40, "ANCESTOR_STATUS": "1"},
        )
        for values in cases:
            with self.subTest(values=values):
                result, output = self.run_snapshot(**values)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(output, "base=\n")

    def run_image(
        self,
        event: str,
        *,
        tag_exists: bool,
        inputs_changed: bool,
        manifest=None,
        require_image=False,
    ):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            output = root / "output"
            (root / "git").write_text(
                """#!/usr/bin/env bash
if [[ "$1" == cat-file ]]; then exit 0; fi
if [[ "$1" == diff ]]; then
  [[ "${INPUTS_CHANGED:-false}" == true ]] && exit 1
  exit 0
fi
exit 2
""",
                encoding="utf-8",
            )
            (root / "docker").write_text(
                """#!/usr/bin/env bash
[[ "${TAG_EXISTS:-false}" == true ]] || exit 1
printf '%s\\n' "$MANIFEST"
""",
                encoding="utf-8",
            )
            (root / "git").chmod(0o755)
            (root / "docker").chmod(0o755)
            env = {
                **os.environ,
                "GITHUB_OUTPUT": str(output),
                "IMAGE_NAME": "ghcr.io/example/latex",
                "RELEASE_TAG": "immutable",
                "TAG_EXISTS": str(tag_exists).lower(),
                "INPUTS_CHANGED": str(inputs_changed).lower(),
                "REQUIRE_IMAGE": str(require_image).lower(),
                "MANIFEST": manifest
                if manifest is not None
                else json.dumps(
                    {
                        "manifests": [
                            {"platform": {"os": "linux", "architecture": arch}}
                            for arch in ("amd64", "arm64")
                        ]
                    }
                ),
                "PATH": f"{root}:{os.environ['PATH']}",
            }
            result = subprocess.run(
                [ROOT / "scripts/check-image-tag.sh", event, "base", "head"],
                cwd=ROOT,
                env=env,
                text=True,
                capture_output=True,
                check=False,
            )
            return result, output.read_text(encoding="utf-8") if output.exists() else ""

    def test_new_image_tag_builds(self):
        result, output = self.run_image("push", tag_exists=False, inputs_changed=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "exists=false\n")

    def test_existing_content_tag_is_reused(self):
        result, output = self.run_image("push", tag_exists=True, inputs_changed=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "exists=true\n")

    def test_existing_tag_with_workflow_only_change_succeeds(self):
        result, output = self.run_image("push", tag_exists=True, inputs_changed=False)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "exists=true\n")

    def test_dispatch_never_overwrites_existing_tag(self):
        result, output = self.run_image(
            "workflow_dispatch", tag_exists=True, inputs_changed=True
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "exists=true\n")

    def test_build_image_triggers_cover_tag_and_image_inputs(self):
        wrapper = (ROOT / ".github/workflows/build-image.yml").read_text(
            encoding="utf-8"
        )
        text = (ROOT / ".github/workflows/prepare-image.yml").read_text(
            encoding="utf-8"
        )
        for path in (
            ".devcontainer/Dockerfile",
            "config/toolchain.env",
            "scripts/check-toolchain.sh",
        ):
            self.assertIn(path, text)
        self.assertNotIn("scripts/check-environment.sh", text)
        self.assertIn("cut -c 1-12", text)
        self.assertIn("RELEASE_TAG=texlive-${input_hash}", text)
        self.assertNotIn("pull_request_target:", wrapper)
        self.assertIn("workflow_dispatch:", wrapper)
        self.assertIn("if: needs.prepare.outputs.exists != 'true'", text)
        self.assertIn('make image pin DIGEST="$DIGEST"', wrapper)
        self.assertIn("prepare-image.yml", wrapper)

    def test_immutable_tag_check_covers_only_image_inputs(self):
        text = (ROOT / ".github/workflows/prepare-image.yml").read_text(
            encoding="utf-8"
        )
        self.assertIn(
            ".devcontainer/Dockerfile",
            text,
        )
        self.assertIn("config/toolchain.env", text)
        self.assertIn("scripts/check-toolchain.sh", text)
        self.assertNotIn("scripts/check-environment.sh", text)

    def test_source_check_always_runs_unit_tests(self):
        workflow = yaml.safe_load(
            (ROOT / ".github/workflows/build.yml").read_text(encoding="utf-8")
        )
        unit_test = next(
            step
            for step in workflow["jobs"]["source"]["steps"]
            if step.get("name") == "Unit tests"
        )
        self.assertEqual(unit_test["run"], "make test")
        self.assertNotIn("if", unit_test)

    def test_source_job_defers_lean_checks_to_its_lean_step(self):
        workflow = yaml.safe_load(
            (ROOT / ".github/workflows/build.yml").read_text(encoding="utf-8")
        )
        steps = workflow["jobs"]["source"]["steps"]
        lean = next(
            i for i, step in enumerate(steps) if step.get("run") == "make lean check"
        )
        repository = next(
            i
            for i, step in enumerate(steps)
            if step.get("run") == "./scripts/check-repository.sh --defer-lean"
        )
        self.assertLess(lean, repository)
        self.assertNotIn("if", steps[lean])
        self.assertNotIn("continue-on-error", steps[lean])

    def test_source_check_uses_supported_lean_make_contract(self):
        workflow = yaml.safe_load(
            (ROOT / ".github/workflows/build.yml").read_text(encoding="utf-8")
        )
        lean_check = next(
            step
            for step in workflow["jobs"]["source"]["steps"]
            if step.get("name") == "Check Lean proofs and LaTeX links"
        )
        self.assertEqual(lean_check["run"], "make lean check")
        result = subprocess.run(
            ["make", "-n", "lean", "check"],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("./scripts/check-lean.sh", result.stdout)

    def test_source_checks_run_independently_of_image_preparation(self):
        workflow = yaml.safe_load(
            (ROOT / ".github/workflows/build.yml").read_text(encoding="utf-8")
        )
        self.assertNotIn("needs", workflow["jobs"]["source"])
        self.assertEqual(workflow["jobs"]["latex"]["needs"], "prepare-image")
        self.assertEqual(workflow["jobs"]["check"]["needs"], ["source", "latex"])

    def test_external_actions_are_pinned_to_full_commit_shas(self):
        reference = re.compile(r"^[^/@]+/[^/@]+(?:/[^/@]+)*@[0-9a-f]{40}$")
        paths = sorted((ROOT / ".github/workflows").glob("*.yml"))
        paths += sorted((ROOT / ".github/actions").rglob("action.yml"))
        for path in paths:
            workflow = yaml.safe_load(path.read_text(encoding="utf-8"))
            pending = [workflow]
            while pending:
                value = pending.pop()
                if isinstance(value, dict):
                    uses = value.get("uses")
                    if isinstance(uses, str) and not uses.startswith("./"):
                        self.assertRegex(uses, reference, f"{path}: {uses}")
                    pending.extend(value.values())
                elif isinstance(value, list):
                    pending.extend(value)

    def test_pages_generation_is_not_immediately_rechecked(self):
        workflow = yaml.safe_load(
            (ROOT / ".github/workflows/pages.yml").read_text(encoding="utf-8")
        )
        generation = next(
            step
            for step in workflow["jobs"]["deploy"]["steps"]
            if step.get("name") == "Validate and generate site from books.yml"
        )
        self.assertEqual(generation["run"], "make site")

    def test_build_trigger_delegates_path_classification_to_planner(self):
        workflow = self.build_workflow()
        self.assertNotIn("paths-ignore", workflow[True]["pull_request"] or {})
        self.assertNotIn("paths-ignore", workflow[True]["push"])

    def test_image_builds_and_publication_are_gated(self):
        workflow = yaml.safe_load(
            (ROOT / ".github/workflows/prepare-image.yml").read_text(encoding="utf-8")
        )
        jobs = workflow["jobs"]
        self.assertEqual(jobs["build"]["needs"], "prepare")
        self.assertEqual(jobs["build"]["if"], "needs.prepare.outputs.exists != 'true'")
        self.assertEqual(
            jobs["build"]["strategy"]["matrix"]["include"],
            [
                {"arch": "amd64", "runner": "ubuntu-24.04"},
                {"arch": "arm64", "runner": "ubuntu-24.04-arm"},
            ],
        )
        steps = jobs["build"]["steps"]
        build = next(
            step
            for step in steps
            if step.get("name") == "Build image for smoke testing"
        )
        self.assertEqual(build["with"]["platforms"], "linux/${{ matrix.arch }}")
        names = [step.get("name") for step in steps]
        self.assertLess(
            names.index("Smoke test the image toolchain"),
            names.index("Push the tested image and record its digest"),
        )
        self.assertEqual(jobs["publish"]["needs"], ["prepare", "build"])
        self.assertIn("needs.build.result == 'success'", jobs["publish"]["if"])
        self.assertIn("needs.prepare.outputs.exists == 'true'", jobs["publish"]["if"])
        self.assertIn("!cancelled()", jobs["publish"]["if"])
        self.assertNotIn(
            "Login to GitHub Container Registry",
            [step.get("name") for step in jobs["prepare"]["steps"]],
        )

    def test_pr_images_do_not_use_registry_credentials_or_publish(self):
        workflow = yaml.safe_load(
            (ROOT / ".github/workflows/prepare-image.yml").read_text()
        )
        for job in workflow["jobs"].values():
            for step in job.get("steps", []):
                if (
                    "login-action@" in step.get("uses", "")
                    or "docker push" in step.get("run", "")
                    or "imagetools create" in step.get("run", "")
                ):
                    with self.subTest(step=step.get("name")):
                        self.assertIn("github.event_name != 'pull_request'", step["if"])
        build_steps = workflow["jobs"]["build"]["steps"]
        archive = next(
            step for step in build_steps if "docker save" in step.get("run", "")
        )
        self.assertIn("github.event_name == 'pull_request'", archive["if"])
        self.assertIn("matrix.arch == 'amd64'", archive["if"])
        for name in ("latex", "book"):
            steps = self.build_workflow()["jobs"][name]["steps"]
            loader = next(
                index
                for index, step in enumerate(steps)
                if step.get("uses") == "./.github/actions/load-toolchain"
            )
            consumer = next(
                index
                for index, step in enumerate(steps)
                if "texlive-action@" in step.get("uses", "")
            )
            self.assertLess(loader, consumer)
        for step in self.build_workflow()["jobs"]["book"]["steps"]:
            if step.get("name") in {
                "Record the verified build",
                "Upload verified build for reuse after merge",
            }:
                self.assertIn("needs.prepare-image.outputs.artifact == ''", step["if"])

    def test_run_local_image_selection_does_not_access_the_registry(self):
        workflow = yaml.safe_load(
            (ROOT / ".github/workflows/prepare-image.yml").read_text()
        )
        script = next(
            step["run"]
            for step in workflow["jobs"]["publish"]["steps"]
            if step.get("id") == "image"
        )
        for digest, success in (("sha256:" + "a" * 64, True), ("invalid", False)):
            with (
                self.subTest(digest=digest),
                tempfile.TemporaryDirectory() as temporary,
            ):
                root = Path(temporary)
                (root / "build/image-digests").mkdir(parents=True)
                (root / "build/image-digests/amd64").write_text(digest + "\n")
                docker = root / "docker"
                docker.write_text("#!/bin/sh\nexit 99\n")
                docker.chmod(0o755)
                output = root / "output"
                result = subprocess.run(
                    ["bash", "-euo", "pipefail", "-c", script],
                    cwd=root,
                    env={
                        **os.environ,
                        "PATH": f"{root}:{os.environ['PATH']}",
                        "GITHUB_EVENT_NAME": "pull_request",
                        "GITHUB_OUTPUT": str(output),
                        "GITHUB_RUN_ID": "123",
                        "GITHUB_RUN_ATTEMPT": "2",
                        "IMAGE_NAME": "ghcr.io/example/toolchain",
                    },
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(result.returncode == 0, success, result.stderr)
                if success:
                    self.assertEqual(
                        output.read_text(),
                        f"digest={'a' * 64}\n"
                        "reference=ghcr.io/example/toolchain:build-123-2-amd64\n",
                    )
                else:
                    self.assertFalse(output.exists())

    def test_loaded_image_must_match_identity_and_architecture(self):
        action = yaml.safe_load(
            (ROOT / ".github/actions/load-toolchain/action.yml").read_text()
        )
        script = action["runs"]["steps"][-1]["run"]
        for image_id, arch, success in (
            ("sha256:" + "a" * 64, "amd64", True),
            ("sha256:" + "b" * 64, "amd64", False),
            ("sha256:" + "a" * 64, "arm64", False),
        ):
            with self.subTest(image=image_id, arch=arch):
                with tempfile.TemporaryDirectory() as temporary:
                    root = Path(temporary)
                    archive = root / "image.tar.gz"
                    archive.touch()
                    docker = root / "docker"
                    docker.write_text(
                        "#!/usr/bin/env bash\n"
                        'if [[ "$1" == load ]]; then exit 0; fi\n'
                        'case "$5" in\n'
                        "  '{{.Id}}') echo \"$IMAGE_ID\" ;;\n"
                        "  '{{.Architecture}}') echo \"$IMAGE_ARCH\" ;;\n"
                        "  *) exit 2 ;;\n"
                        "esac\n"
                    )
                    docker.chmod(0o755)
                    result = subprocess.run(
                        ["bash", "-euo", "pipefail", "-c", script],
                        env={
                            **os.environ,
                            "PATH": f"{root}:{os.environ['PATH']}",
                            "ARCHIVE": str(archive),
                            "IMAGE": "ghcr.io/example/toolchain:local",
                            "DIGEST": "a" * 64,
                            "IMAGE_ID": image_id,
                            "IMAGE_ARCH": arch,
                        },
                        capture_output=True,
                        text=True,
                        check=False,
                    )
                    self.assertEqual(result.returncode == 0, success, result.stderr)
                    self.assertEqual(archive.exists(), not success)

    def test_image_pin_requires_combined_checks(self):
        job = self.build_workflow()["jobs"]["pin-image"]
        self.assertEqual(job["needs"], ["prepare-image", "check", "build-check"])
        self.assertNotIn("always()", job["if"])

    def test_incomplete_or_invalid_existing_images_are_not_reused(self):
        manifests = [
            {},
            {"manifests": [{"platform": {"os": "linux", "architecture": "amd64"}}]},
            {"manifests": [{"platform": {"os": "linux", "architecture": "arm64"}}]},
            {
                "manifests": [
                    {"platform": {"os": "linux", "architecture": "amd64"}},
                    {"platform": {"os": "windows", "architecture": "arm64"}},
                ]
            },
        ]
        for manifest in [*(json.dumps(value) for value in manifests), "not json"]:
            with self.subTest(manifest=manifest):
                result, output = self.run_image(
                    "push", tag_exists=True, inputs_changed=False, manifest=manifest
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(output, "")
                self.assertIn("immutable tags must not be overwritten", result.stderr)

    def test_required_published_image_cannot_be_missing(self):
        result, output = self.run_image(
            "push", tag_exists=False, inputs_changed=False, require_image=True
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(output, "")

    def test_attestation_descriptors_do_not_prevent_reuse(self):
        manifest = {
            "manifests": [
                {"platform": {"os": "linux", "architecture": "amd64"}},
                {"platform": {"os": "linux", "architecture": "arm64"}},
                {"platform": {"os": "unknown", "architecture": "unknown"}},
            ]
        }
        result, output = self.run_image(
            "push", tag_exists=True, inputs_changed=False, manifest=json.dumps(manifest)
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "exists=true\n")

    def test_publish_skips_changes_without_pdf_or_site_impact(self):
        condition = self.build_workflow()["jobs"]["publish"]["if"]
        self.assertIn("needs.plan.outputs.count != '0'", condition)
        self.assertIn("needs.plan.outputs.site_changed == 'true'", condition)
        self.assertIn("needs.plan.outputs.snapshot_changed == 'true'", condition)

    def test_publish_requires_source_and_build_checks(self):
        publish = self.build_workflow()["jobs"]["publish"]
        for gate in ("check", "build-check"):
            with self.subTest(gate=gate):
                self.assertIn(gate, publish["needs"])
                self.assertIn(f"needs.{gate}.result == 'success'", publish["if"])

    def test_snapshot_readme_change_does_not_redeploy_pages(self):
        condition = self.build_workflow()["jobs"]["pages"]["if"]
        self.assertNotIn("snapshot_changed", condition)

    def test_pdf_artifacts_are_downloaded_into_one_flat_directory(self):
        workflow = self.build_workflow()
        download = workflow["jobs"]["publish"]["steps"][1]
        self.assertEqual(download["with"]["pattern"], "*-pdf")
        self.assertEqual(download["with"]["path"], "updated-pdfs")
        self.assertIs(download["with"]["merge-multiple"], True)
        upload = workflow["jobs"]["book"]["steps"][-1]
        self.assertEqual(
            upload["with"]["path"],
            "build/${{ matrix.book }}/${{ matrix.book }}.pdf",
        )

    def test_pdf_update_accepts_zero_one_and_multiple_inputs(self):
        cases = (
            (
                {},
                {"alpha.pdf": b"old-a", "beta.pdf": b"old-b"},
                {"alpha.pdf": b"old-a", "beta.pdf": b"old-b"},
                [],
            ),
            (
                {"alpha.pdf": b"new-a"},
                {"beta.pdf": b"old-b"},
                {"alpha.pdf": b"new-a", "beta.pdf": b"old-b"},
                ["alpha"],
            ),
            (
                {"alpha.pdf": b"new-a", "beta.pdf": b"new-b"},
                {},
                {"alpha.pdf": b"new-a", "beta.pdf": b"new-b"},
                ["alpha", "beta"],
            ),
        )
        for updated, existing, expected, required in cases:
            with self.subTest(updated=updated):
                result, snapshot, calls = self.run_pdf_update(updated, existing)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(snapshot, expected)
                self.assertEqual(calls, required)
                self.assertNotIn("*", calls)

    def test_pdf_update_prunes_files_that_are_no_longer_for_site(self):
        result, snapshot, _ = self.run_pdf_update(
            {},
            {"alpha.pdf": b"a", "retired.pdf": b"old"},
            registered=("alpha", "retired"),
            site=("alpha",),
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(snapshot, {"alpha.pdf": b"a"})

    def test_pdf_update_rejects_unknown_slug(self):
        result, _, calls = self.run_pdf_update(
            {"unknown.pdf": b"pdf"},
            {"alpha.pdf": b"old-a", "beta.pdf": b"old-b"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, ["unknown"])

    def test_pdf_update_rejects_empty_artifact_before_slug_validation(self):
        result, _, calls = self.run_pdf_update(
            {"alpha.pdf": b""},
            {"alpha.pdf": b"old-a", "beta.pdf": b"old-b"},
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(calls, [])
        self.assertIn("PDF artifact is missing or empty", result.stderr)

    def test_pages_requires_snapshot_source_correspondence(self):
        workflow = yaml.safe_load((ROOT / ".github/workflows/pages.yml").read_text())
        step = next(
            step
            for step in workflow["jobs"]["deploy"]["steps"]
            if step.get("id") == "source"
        )
        for snapshot_sha, call_sha, success in (
            ("a" * 40, "a" * 40, True),
            ("b" * 40, "", True),
            ("a" * 40, "b" * 40, False),
            ("invalid", "", False),
            ("", "", False),
            (None, "", False),
        ):
            with (
                self.subTest(snapshot=snapshot_sha, call=call_sha),
                tempfile.TemporaryDirectory() as temporary,
            ):
                root = Path(temporary)
                output = root / "output"
                (root / "pdf-snapshot").mkdir()
                if snapshot_sha is not None:
                    (root / "pdf-snapshot/.source-sha").write_text(snapshot_sha + "\n")
                result = subprocess.run(
                    ["bash", "-euo", "pipefail", "-c", step["run"]],
                    cwd=root,
                    env={
                        **os.environ,
                        "CALL_SHA": call_sha,
                        "GITHUB_OUTPUT": str(output),
                    },
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=10,
                )
                self.assertEqual(result.returncode == 0, success, result.stderr)
                if success:
                    self.assertEqual(output.read_text(), f"sha={snapshot_sha}\n")
                else:
                    self.assertFalse(output.exists())

    def test_source_gate_rejects_unsuccessful_dependencies(self):
        job = self.build_workflow()["jobs"]["check"]
        self.assertEqual(job["if"], "always()")
        for source, latex in itertools.product(
            ("success", "failure", "cancelled", "skipped"), repeat=2
        ):
            with self.subTest(source=source, latex=latex):
                result = subprocess.run(
                    ["bash", "-euo", "pipefail", "-c", job["steps"][0]["run"]],
                    env={**os.environ, "SOURCE_RESULT": source, "LATEX_RESULT": latex},
                    capture_output=True,
                    text=True,
                    check=False,
                    timeout=10,
                )
                self.assertEqual(result.returncode == 0, source == latex == "success")

    def test_all_workflow_shell_blocks_parse(self):
        expression = re.compile(r"\$\{\{.*?\}\}", re.DOTALL)
        for workflow in sorted((ROOT / ".github/workflows").glob("*.yml")):
            document = yaml.safe_load(workflow.read_text(encoding="utf-8"))
            workflow_shell = (
                document.get("defaults", {}).get("run", {}).get("shell", "bash")
            )
            for job_name, job in document["jobs"].items():
                job_shell = (
                    job.get("defaults", {}).get("run", {}).get("shell", workflow_shell)
                )
                for number, step in enumerate(job.get("steps", []), 1):
                    # Only executable run blocks are shell code; metadata, action
                    # arguments, and multiline expressions are not shell scripts.
                    script = step.get("run")
                    if script is None and step.get("uses", "").startswith(
                        "xu-cheng/texlive-action@"
                    ):
                        script = step["with"]["run"]
                    if script is None:
                        continue
                    shell = step.get("shell", job_shell)
                    if shell.split()[0] not in {"bash", "sh"}:
                        continue
                    script = expression.sub("workflow_value", script)
                    with self.subTest(
                        workflow=workflow.name, job=job_name, step=number
                    ):
                        result = subprocess.run(
                            [shell.split()[0], "-n"],
                            input=script,
                            text=True,
                            capture_output=True,
                            check=False,
                            timeout=10,
                        )
                        self.assertEqual(
                            result.returncode, 0, f"{result.stderr}\n{script}"
                        )


if __name__ == "__main__":
    unittest.main()
