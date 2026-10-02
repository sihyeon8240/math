"""Source gates, workflow wiring, and inline shell syntax."""

from __future__ import annotations

import itertools
import os
import re
import subprocess
import unittest
from pathlib import Path

import yaml
from workflow_support import build_workflow

ROOT = Path(__file__).resolve().parent.parent


class WorkflowContractTests(unittest.TestCase):
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
            timeout=30,
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

    def test_build_trigger_delegates_path_classification_to_planner(self):
        workflow = build_workflow()
        self.assertNotIn("paths-ignore", workflow[True]["pull_request"] or {})
        self.assertNotIn("paths-ignore", workflow[True]["push"])

    def test_source_gate_rejects_unsuccessful_dependencies(self):
        job = build_workflow()["jobs"]["check"]
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
