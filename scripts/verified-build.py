#!/usr/bin/env python3
"""Record strict PDF builds and conservatively reuse merged PR artifacts."""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
import re
import subprocess
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
POLICY = "strict-pdf-v1"
FILES = ("book.pdf", "book.log")
MAX_BYTES = 100 * 1024 * 1024


def command(*args: str) -> bytes:
    return subprocess.run(
        args, cwd=ROOT, check=True, capture_output=True, timeout=60
    ).stdout


def api(endpoint: str):
    return json.loads(command("gh", "api", endpoint))


def identity(book: str, image: str) -> dict:
    if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", book):
        raise ValueError("invalid book slug")
    if not re.fullmatch(r"ghcr\.io/[a-z0-9/_.-]+@sha256:[0-9a-f]{64}", image):
        raise ValueError("an immutable image digest is required")
    return {
        "policy": POLICY,
        "book": book,
        "image": image,
        "platform": "linux/amd64",
        "tree": command("git", "rev-parse", "HEAD^{tree}").decode().strip(),
    }


def checksum(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def record(expected: dict, directory: Path) -> None:
    command("python3", "scripts/check-log.py", "--strict", str(directory / "book.log"))
    files = {name: (directory / name).read_bytes() for name in FILES}
    if not files["book.pdf"].startswith(b"%PDF-"):
        raise ValueError("build did not produce a PDF")
    manifest = {
        **expected,
        "run_id": os.environ["GITHUB_RUN_ID"],
        "run_attempt": os.environ["GITHUB_RUN_ATTEMPT"],
        "checksums": {name: checksum(data) for name, data in files.items()},
    }
    (directory / "verified-build.json").write_text(
        json.dumps(manifest, sort_keys=True) + "\n", encoding="utf-8"
    )


def eligible_run(run: dict, repository: str, head: str) -> bool:
    return (
        run.get("event") == "pull_request"
        and run.get("status") == "completed"
        and run.get("conclusion") == "success"
        and run.get("head_sha") == head
        and (run.get("head_repository") or {}).get("full_name") == repository
        and run.get("path") == ".github/workflows/build.yml"
    )


def verify_archive(data: bytes, expected: dict, run: dict) -> dict[str, bytes]:
    if len(data) > MAX_BYTES:
        raise ValueError("artifact is too large")
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        names = [*FILES, "verified-build.json"]
        if sorted(archive.namelist()) != sorted(names):
            raise ValueError("unexpected artifact files")
        if sum(info.file_size for info in archive.infolist()) > MAX_BYTES:
            raise ValueError("expanded artifact is too large")
        manifest = json.loads(archive.read("verified-build.json"))
        if not isinstance(manifest, dict):
            raise ValueError("invalid build manifest")
        for key, value in expected.items():
            if manifest.get(key) != value:
                raise ValueError(f"build identity differs: {key}")
        if manifest.get("run_id") != str(run["id"]) or manifest.get(
            "run_attempt"
        ) != str(run["run_attempt"]):
            raise ValueError("build belongs to a different run or attempt")
        files = {name: archive.read(name) for name in FILES}
        if manifest.get("checksums") != {
            name: checksum(content) for name, content in files.items()
        }:
            raise ValueError("artifact checksum mismatch")
        if not files["book.pdf"].startswith(b"%PDF-") or not files["book.log"]:
            raise ValueError("missing PDF or build log")
        return files


def restore(expected: dict, directory: Path) -> bool:
    repository = os.environ["GITHUB_REPOSITORY"]
    commit = os.environ["GITHUB_SHA"]
    pulls = api(f"repos/{repository}/commits/{commit}/pulls?per_page=100")
    for pull in pulls:
        if (
            not pull.get("merged_at")
            or pull.get("merge_commit_sha") != commit
            or pull.get("base", {}).get("ref") != "main"
            or (pull.get("head", {}).get("repo") or {}).get("full_name") != repository
        ):
            continue
        head = pull["head"]["sha"]
        runs = api(
            f"repos/{repository}/actions/workflows/build.yml/runs"
            f"?event=pull_request&status=success&head_sha={head}&per_page=30"
        )["workflow_runs"]
        for run in runs:
            if not eligible_run(run, repository, head):
                continue
            artifacts = api(
                f"repos/{repository}/actions/runs/{run['id']}/artifacts?per_page=100"
            )["artifacts"]
            for artifact in artifacts:
                if (
                    artifact["name"] != f"{expected['book']}-verified-build"
                    or artifact.get("expired", True)
                    or artifact.get("size_in_bytes", MAX_BYTES + 1) > MAX_BYTES
                ):
                    continue
                try:
                    data = command(
                        "gh",
                        "api",
                        f"repos/{repository}/actions/artifacts/{artifact['id']}/zip",
                    )
                    if artifact.get("digest") != f"sha256:{checksum(data)}":
                        raise ValueError("GitHub artifact digest mismatch")
                    files = verify_archive(data, expected, run)
                    directory.mkdir(parents=True, exist_ok=True)
                    for name, content in files.items():
                        (directory / name).write_bytes(content)
                    command(
                        "python3",
                        "scripts/check-log.py",
                        "--strict",
                        str(directory / "book.log"),
                    )
                    print(
                        f"Reused verified PDF from PR #{pull['number']}, run {run['id']}"
                    )
                    return True
                except (
                    ValueError,
                    KeyError,
                    OSError,
                    zipfile.BadZipFile,
                    subprocess.SubprocessError,
                ) as error:
                    print(f"Artifact cannot be reused; rebuilding: {error}")
    return False


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("record", "restore"))
    parser.add_argument("--book", required=True)
    parser.add_argument("--image", required=True)
    args = parser.parse_args()
    expected = identity(args.book, args.image)
    directory = ROOT / "build" / args.book
    if args.mode == "record":
        record(expected, directory)
        return
    reused = False
    try:
        reused = restore(expected, directory)
    except (ValueError, KeyError, OSError, subprocess.SubprocessError) as error:
        print(f"PR artifact lookup unavailable; rebuilding: {error}")
    with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as output:
        output.write(f"reused={str(reused).lower()}\n")


if __name__ == "__main__":
    main()
