"""Exercise image pin retries against a local Git remote and a fake PR API."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class ImagePinPrTests(unittest.TestCase):
    def run_pin(
        self,
        *,
        existing_pr="",
        branch="",
        changed=True,
        stale=False,
        different_tree=False,
    ):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            remote = root / "remote.git"
            work = root / "work"
            work.mkdir()
            env = {
                **os.environ,
                "GIT_CONFIG_GLOBAL": os.devnull,
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_AUTHOR_NAME": "Test",
                "GIT_AUTHOR_EMAIL": "test@example.com",
                "GIT_COMMITTER_NAME": "Test",
                "GIT_COMMITTER_EMAIL": "test@example.com",
            }

            def git(*args, cwd=work):
                return subprocess.run(
                    ["git", *args],
                    cwd=cwd,
                    env=env,
                    capture_output=True,
                    text=True,
                    check=True,
                    timeout=10,
                ).stdout.strip()

            git("init", "--bare", "--initial-branch=main", str(remote))
            git("init", "--initial-branch=main")
            git("remote", "add", "origin", str(remote))
            (work / "config").mkdir()
            (work / ".devcontainer").mkdir()
            pin = work / "config/container-image.txt"
            container = work / ".devcontainer/devcontainer.json"
            pin.write_text("old-image\n")
            container.write_text('{"image": "old-image"}\n')
            git("add", ".")
            git("commit", "-m", "Initial source")
            sha = git("rev-parse", "HEAD")
            git("push", "origin", "main")

            if changed:
                pin.write_text("new-image\n")
                container.write_text('{"image": "new-image"}\n')
            if branch:
                git("add", ".")
                git("commit", "-m", "Previous attempt")
                git("push", "origin", f"HEAD:refs/heads/{branch}")
                git("reset", "--mixed", sha)
                if different_tree:
                    pin.write_text("different-image\n")
            if stale:
                (work / "new-source").touch()
                git("add", "new-source")
                git("commit", "-m", "Newer main")
                git("push", "origin", "main")
                git("reset", "--mixed", sha)

            gh = root / "gh"
            gh.write_text(
                """#!/usr/bin/env python3
import json
import os
import sys
from pathlib import Path

args = sys.argv[1:]
with open(os.environ["PR_LOG"], "a", encoding="utf-8") as log:
    log.write(json.dumps(args) + "\\n")
if args[:2] == ["pr", "list"]:
    if "--head" in args:
        print(os.environ["EXISTING_PR"])
    elif os.environ["OPEN_BRANCH"]:
        print(os.environ["OPEN_BRANCH"] + "\\thttps://example.com/pr/old")
elif args[:2] == ["pr", "create"]:
    body = Path(args[args.index("--body-file") + 1]).read_text()
    Path(os.environ["BODY_LOG"]).write_text(body)
    print("https://example.com/pr/new")
else:
    raise SystemExit(2)
"""
            )
            gh.chmod(0o755)
            log = root / "pr.log"
            body_log = root / "body.log"
            result = subprocess.run(
                [ROOT / "scripts/open-image-pin-pr.sh"],
                cwd=work,
                env={
                    **env,
                    "PATH": f"{root}:{env['PATH']}",
                    "GITHUB_SHA": sha,
                    "GITHUB_RUN_ID": "123",
                    "EXISTING_PR": existing_pr,
                    "OPEN_BRANCH": branch if branch.endswith("456") else "",
                    "PR_LOG": str(log),
                    "BODY_LOG": str(body_log),
                },
                capture_output=True,
                text=True,
                check=False,
                timeout=10,
            )
            calls = (
                [json.loads(line) for line in log.read_text().splitlines()]
                if log.exists()
                else []
            )
            refs = git("ls-remote", "--heads", "origin", "automation/image-pin-123")
            body = body_log.read_text() if body_log.exists() else ""
            return result, calls, refs, body

    def test_new_pr_pushes_a_branch_and_explains_ci_approval(self):
        result, calls, refs, body = self.run_pin()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(refs.endswith("refs/heads/automation/image-pin-123"))
        self.assertEqual(sum(call[:2] == ["pr", "create"] for call in calls), 1)
        self.assertIn("Approve workflows to run", body)

    def test_no_changes_or_stale_main_do_not_create_prs(self):
        for values in ({"changed": False}, {"stale": True}):
            with self.subTest(values=values):
                result, calls, refs, _ = self.run_pin(**values)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(calls, [])
                self.assertEqual(refs, "")

    def test_existing_pr_is_not_recreated(self):
        result, calls, refs, _ = self.run_pin(existing_pr="https://example.com/pr/old")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(calls), 1)
        self.assertEqual(refs, "")

    def test_already_pushed_branch_can_finish_pr_creation(self):
        result, calls, refs, _ = self.run_pin(branch="automation/image-pin-123")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(refs)
        self.assertEqual(sum(call[:2] == ["pr", "create"] for call in calls), 1)

    def test_another_open_pr_for_the_same_image_is_reused(self):
        result, calls, refs, _ = self.run_pin(branch="automation/image-pin-456")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(any(call[:2] == ["pr", "create"] for call in calls))
        self.assertEqual(refs, "")

    def test_retry_does_not_overwrite_an_existing_branch_with_different_contents(self):
        result, calls, refs, _ = self.run_pin(
            branch="automation/image-pin-123", different_tree=True
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("different contents", result.stderr)
        self.assertTrue(refs)
        self.assertFalse(any(call[:2] == ["pr", "create"] for call in calls))


if __name__ == "__main__":
    unittest.main()
