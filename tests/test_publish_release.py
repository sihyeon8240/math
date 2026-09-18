"""Publication integration tests using a local Git remote and a fake GitHub API."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class PublishReleaseTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.git("init", "-b", "main")
        self.git("config", "user.name", "Test")
        self.git("config", "user.email", "test@example.invalid")
        scripts = self.repo / "scripts"
        scripts.mkdir()
        for name in ["publish-release.sh", "upload-release-assets.sh"]:
            shutil.copy2(ROOT / "scripts" / name, scripts / name)
        (scripts / "books.py").write_text('print("1.1.0")\n')
        validator = scripts / "release-plan.sh"
        validator.write_text("#!/usr/bin/env bash\nexit 0\n")
        validator.chmod(0o755)
        self.git("add", ".")
        self.git("commit", "-m", "Initial")
        self.sha = self.git("rev-parse", "HEAD")
        origin = self.root / "origin.git"
        subprocess.run(
            ["git", "init", "--bare", str(origin)], check=True, capture_output=True
        )
        self.git("remote", "add", "origin", str(origin))
        self.git("push", "origin", "main")
        self.package = self.repo / "build" / "release"
        self.package.mkdir(parents=True)
        self.tag = "alpha-v1.1.0"
        self.pdf = self.package / f"{self.tag}.pdf"
        self.pdf.write_bytes(b"%PDF-test")
        self.checksum = self.package / "SHA256SUMS"
        self.checksum.write_text(
            f"{hashlib.sha256(self.pdf.read_bytes()).hexdigest()}  {self.pdf.name}\n"
        )
        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.state = self.root / "state.json"
        self.state.write_text(json.dumps({"draft": None, "assets": {}, "calls": []}))
        gh = self.bin / "gh"
        gh.write_text("""#!/usr/bin/env python3
import json
import os
import pathlib
import sys
path = pathlib.Path(os.environ["FAKE_GH_STATE"])
s = json.loads(path.read_text())
a = sys.argv[1:]
s["calls"].append(a)
path.write_text(json.dumps(s))
if os.environ.get("FAIL_GH") == " ".join(a[:2]):
    sys.exit(1)
if a[0] == "api":
    if s["draft"] is not None:
        print(str(s["draft"]).lower())
elif a[:2] == ["release", "create"]:
    s["draft"] = True
elif a[:2] == ["release", "view"]:
    print("\\n".join(s["assets"]))
elif a[:2] == ["release", "upload"]:
    for name in a[3:]:
        p = pathlib.Path(name)
        s["assets"][p.name] = p.read_bytes().hex()
elif a[:2] == ["release", "download"]:
    dest = pathlib.Path(a[a.index("--dir") + 1])
    for i, arg in enumerate(a):
        if arg == "--pattern":
            name = a[i + 1]
            (dest / name).write_bytes(bytes.fromhex(s["assets"][name]))
elif a[:2] == ["release", "edit"]:
    assert "--draft=false" in a
    s["draft"] = False
else:
    sys.exit(98)
path.write_text(json.dumps(s))
""")
        gh.chmod(0o755)

    def tearDown(self):
        self.temporary.cleanup()

    def git(self, *args):
        return subprocess.check_output(
            ["git", *args], cwd=self.repo, text=True, stderr=subprocess.DEVNULL
        ).strip()

    def run_publish(self, **env):
        return subprocess.run(
            [str(self.repo / "scripts/publish-release.sh"), "alpha", str(self.package)],
            cwd=self.repo,
            env={
                **os.environ,
                "PATH": f"{self.bin}:{os.environ['PATH']}",
                "GITHUB_ACTIONS": "true",
                "GITHUB_EVENT_NAME": "push",
                "GITHUB_REF": "refs/heads/main",
                "GITHUB_SHA": self.sha,
                "GITHUB_REPOSITORY": "owner/test",
                "FAKE_GH_STATE": str(self.state),
                **env,
            },
            text=True,
            capture_output=True,
        )

    def test_success_publishes_verified_assets_and_retry_is_noop(self):
        result = self.run_publish()
        self.assertEqual(result.returncode, 0, result.stderr)
        state = json.loads(self.state.read_text())
        self.assertFalse(state["draft"])
        self.assertEqual(set(state["assets"]), {self.pdf.name, "SHA256SUMS"})
        self.assertEqual(self.git("cat-file", "-t", f"refs/tags/{self.tag}"), "tag")
        self.assertEqual(self.git("rev-list", "-n", "1", self.tag), self.sha)
        count = len(state["calls"])
        result = self.run_publish()
        self.assertEqual(result.returncode, 0, result.stderr)
        calls = json.loads(self.state.read_text())["calls"][count:]
        self.assertTrue(all(c[0] == "api" for c in calls))

    def test_interrupted_upload_resumes_original_package(self):
        failed = self.run_publish(FAIL_GH="release upload")
        self.assertNotEqual(failed.returncode, 0)
        self.assertTrue(json.loads(self.state.read_text())["draft"])
        resumed = self.run_publish()
        self.assertEqual(resumed.returncode, 0, resumed.stderr)
        self.assertFalse(json.loads(self.state.read_text())["draft"])

    def test_conflicting_asset_is_not_overwritten_or_published(self):
        self.state.write_text(
            json.dumps(
                {
                    "draft": True,
                    "assets": {self.pdf.name: b"different".hex()},
                    "calls": [],
                }
            )
        )
        result = self.run_publish()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("different content", result.stderr)
        state = json.loads(self.state.read_text())
        self.assertTrue(state["draft"])
        self.assertFalse(
            any(
                c[:2] in [["release", "edit"], ["release", "upload"]]
                for c in state["calls"]
            )
        )

    def test_non_main_and_wrong_checkout_fail_before_remote_writes(self):
        for env in [
            {"GITHUB_REF": "refs/heads/local-work"},
            {"GITHUB_EVENT_NAME": "pull_request"},
            {"GITHUB_SHA": "0" * 40},
        ]:
            result = self.run_publish(**env)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(json.loads(self.state.read_text())["calls"], [])
            self.assertEqual(self.git("tag", "--list"), "")

    def test_conflicting_tag_fails(self):
        self.git("tag", self.tag)
        self.git("push", "origin", self.tag)
        result = self.run_publish()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("not annotated", result.stderr)
        self.assertEqual(json.loads(self.state.read_text())["calls"], [])

    def test_tampered_package_fails_before_tagging(self):
        self.pdf.write_bytes(b"changed")
        result = self.run_publish()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.git("tag", "--list"), "")

    def test_advanced_main_still_tags_validated_commit(self):
        self.git("commit", "--allow-empty", "-m", "Later main")
        self.git("push", "origin", "main")
        self.git("checkout", "--detach", self.sha)
        result = self.run_publish()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.git("rev-list", "-n", "1", self.tag), self.sha)

    def test_failed_verification_keeps_draft(self):
        result = self.run_publish(FAIL_GH="release download")
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue(json.loads(self.state.read_text())["draft"])


if __name__ == "__main__":
    unittest.main()
