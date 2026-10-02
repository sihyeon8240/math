"""Image selection, build isolation, and publication gates."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

import yaml
from test_support import write_executable
from workflow_support import build_workflow

ROOT = Path(__file__).resolve().parent.parent


class ImageWorkflowTests(unittest.TestCase):
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
                timeout=30,
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
            steps = build_workflow()["jobs"][name]["steps"]
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
        for step in build_workflow()["jobs"]["book"]["steps"]:
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
                write_executable(docker, "#!/bin/sh\nexit 99\n")
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
                    timeout=30,
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
                    write_executable(
                        docker,
                        "#!/usr/bin/env bash\n"
                        'if [[ "$1" == load ]]; then exit 0; fi\n'
                        'case "$5" in\n'
                        "  '{{.Id}}') echo \"$IMAGE_ID\" ;;\n"
                        "  '{{.Architecture}}') echo \"$IMAGE_ARCH\" ;;\n"
                        "  *) exit 2 ;;\n"
                        "esac\n",
                    )
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
                        timeout=30,
                    )
                    self.assertEqual(result.returncode == 0, success, result.stderr)
                    self.assertEqual(archive.exists(), not success)

    def test_image_pin_requires_combined_checks(self):
        job = build_workflow()["jobs"]["pin-image"]
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


if __name__ == "__main__":
    unittest.main()
