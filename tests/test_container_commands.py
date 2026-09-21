"""Exercise public container and book commands without a Docker daemon."""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class ContainerCommandTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="math container ")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for directory in ("scripts", "config", "bin", ".devcontainer"):
            (self.root / directory).mkdir()
        shutil.copy2(ROOT / "Makefile", self.root / "Makefile")
        for name in ("build-image.sh", "run-container.sh"):
            shutil.copy2(ROOT / "scripts" / name, self.root / "scripts" / name)
        self.image = "ghcr.io/example/math@sha256:" + "a" * 64
        (self.root / "config/container-image.txt").write_text(self.image + "\n")
        docker = self.root / "bin/docker"
        docker.write_text(
            f"#!{sys.executable}\n"
            "import json, os, sys\n"
            "from pathlib import Path\n"
            "Path(os.environ['DOCKER_ARGUMENTS']).write_text(json.dumps(sys.argv[1:]))\n"
            "sys.exit(int(os.environ.get('DOCKER_EXIT', '0')))\n"
        )
        docker.chmod(0o755)
        self.arguments_path = self.root / "arguments.json"
        self.environment = {
            **os.environ,
            "PATH": f"{self.root / 'bin'}:{os.environ['PATH']}",
            "DOCKER_ARGUMENTS": str(self.arguments_path),
            "XDG_CACHE_HOME": str(self.root / "cache"),
            "IMAGE": "",
            "CMD": "",
            "PYTHON": sys.executable,
        }

    def make(self, *arguments: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["make", *arguments],
            cwd=self.root,
            env=self.environment,
            capture_output=True,
            text=True,
            check=False,
        )

    def arguments(self) -> list[str]:
        return json.loads(self.arguments_path.read_text())

    def test_build_uses_repository_context_and_custom_tag(self) -> None:
        for options, tag in (
            ([], "math-toolchain:local"),
            (["IMAGE=custom:dev"], "custom:dev"),
        ):
            with self.subTest(tag=tag):
                result = self.make("image", "build", *options)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(
                    self.arguments(),
                    [
                        "build",
                        "--tag",
                        tag,
                        "--file",
                        str(self.root / ".devcontainer/Dockerfile"),
                        str(self.root),
                    ],
                )

    def test_run_mounts_checkout_and_preserves_user_and_cache(self) -> None:
        result = self.make("image", "run")
        self.assertEqual(result.returncode, 0, result.stderr)
        arguments = self.arguments()
        self.assertEqual(arguments[-2:], [self.image, "/bin/zsh"])
        self.assertIn(f"{self.root}:/workspace", arguments)
        self.assertEqual(
            arguments[arguments.index("--user") + 1], f"{os.getuid()}:{os.getgid()}"
        )
        self.assertIn("--interactive", arguments)
        self.assertNotIn("--tty", arguments)
        self.assertIn("HOME=/home/developer", arguments)
        self.assertIn("ELAN_HOME=/home/developer/.elan", arguments)
        self.assertEqual(
            arguments[arguments.index("--entrypoint") + 1],
            "/workspace/scripts/container-entrypoint.sh",
        )
        self.assertIn(
            "TEXINPUTS=.:/workspace/common/styles//:/workspace/common/templates//:",
            arguments,
        )
        homes = list((self.root / "cache/math-container").iterdir())
        self.assertEqual(len(homes), 1)
        marker = homes[0] / "cached"
        marker.write_text("keep")
        self.assertEqual(self.make("image", "run").returncode, 0)
        self.assertEqual(marker.read_text(), "keep")
        self.assertEqual(self.arguments(), arguments)

    def test_command_is_passed_literally_without_host_execution(self) -> None:
        command = 'printf "%s" "$HOME"; touch "$(pwd)/unexpected"'
        result = self.make("image", "run", "IMAGE=custom:dev", f"CMD={command}")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            self.arguments()[-4:], ["custom:dev", "/bin/bash", "-c", command]
        )
        self.assertFalse((self.root / "unexpected").exists())

    def test_direct_script_propagates_exit_status_from_any_directory(self) -> None:
        result = subprocess.run(
            [str(self.root / "scripts/run-container.sh")],
            cwd=self.root / "bin",
            env={**self.environment, "DOCKER_EXIT": "23"},
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 23)
        self.assertIn(f"{self.root}:/workspace", self.arguments())
        self.environment["DOCKER_EXIT"] = "23"
        self.assertNotEqual(self.make("image", "run").returncode, 0)

    def test_tty_is_allocated_for_a_terminal(self) -> None:
        master, slave = os.openpty()
        try:
            result = subprocess.run(
                [str(self.root / "scripts/run-container.sh")],
                env=self.environment,
                stdin=slave,
                stdout=slave,
                stderr=subprocess.PIPE,
                check=False,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("--tty", self.arguments())
        finally:
            os.close(master)
            os.close(slave)

    def test_container_entrypoint_sets_a_writable_lean_home(self) -> None:
        shutil.copy2(
            ROOT / "scripts/container-entrypoint.sh",
            self.root / "scripts/container-entrypoint.sh",
        )
        shutil.copy2(self.root / "bin/docker", self.root / "bin/elan")
        (self.root / "config/toolchain.env").write_text(
            "LEAN_TOOLCHAIN=leanprover/lean4:v99.0.0\n"
        )
        elan_home = self.root / "writable-elan"
        for _ in range(2):
            result = subprocess.run(
                [
                    str(self.root / "scripts/container-entrypoint.sh"),
                    "/bin/sh",
                    "-c",
                    "exit 37",
                ],
                env={**self.environment, "ELAN_HOME": str(elan_home)},
                capture_output=True,
                check=False,
            )
            self.assertEqual(result.returncode, 37, result.stderr)
            self.assertEqual(self.arguments(), ["default", "leanprover/lean4:v99.0.0"])
            self.assertTrue((elan_home / "toolchains").is_dir())

    def test_invalid_subcommands_fail_before_docker_is_called(self) -> None:
        for goals in (
            ("image",),
            ("image", "build", "run"),
            ("image", "run", "check"),
            ("run",),
            ("book", "new", "release"),
            ("book", "new", "check"),
        ):
            with self.subTest(goals=goals):
                result = self.make(*goals)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("usage:", result.stderr)
                self.assertFalse(self.arguments_path.exists())

    def test_book_actions_and_image_pin_dispatch_without_building(self) -> None:
        for script in ("new-book.sh", "releases.py", "check-image-reference.py"):
            shutil.copy2(self.root / "bin/docker", self.root / "scripts" / script)
        cases = [
            (
                ["book", "new", "SLUG=sample", 'TITLE=A "quoted" title'],
                ["sample", 'A "quoted" title'],
            ),
            (
                ["book", "release", "BOOK=sample", "VERSION=1.2.3"],
                ["prepare", "--book", "sample", "--version", "1.2.3"],
            ),
            (["image", "pin", "DIGEST=" + "a" * 64], ["--set-digest", "a" * 64]),
        ]
        for goals, expected in cases:
            with self.subTest(goals=goals):
                result = self.make(*goals)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(self.arguments(), expected)
