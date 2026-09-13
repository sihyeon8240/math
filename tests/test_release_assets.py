"""Retry-safety tests for release asset publication."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import textwrap
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


class ReleaseAssetTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.script = self.root / "upload-release-assets.sh"
        shutil.copy2(ROOT / "scripts/upload-release-assets.sh", self.script)
        self.assets = self.root / "assets"
        self.store = self.root / "store"
        self.bin = self.root / "bin"
        self.assets.mkdir()
        self.store.mkdir()
        self.bin.mkdir()
        self.pdf = self.assets / "alpha-v1.0.0.pdf"
        self.checksums = self.assets / "SHA256SUMS"
        self.pdf.write_bytes(b"pdf")
        self.checksums.write_text("checksum\n", encoding="utf-8")
        gh = self.bin / "gh"
        gh.write_text(
            textwrap.dedent("""\
            #!/usr/bin/env bash
            set -euo pipefail
            case "$1 $2" in
              "release view")
                printf '%s' "${EXISTING_ASSETS:-}"
                ;;
              "release download")
                shift 2
                tag="$1"
                shift
                while (($#)); do
                  case "$1" in
                    --pattern) name="$2"; shift 2 ;;
                    --dir) destination="$2"; shift 2 ;;
                    *) shift ;;
                  esac
                done
                cp "$ASSET_STORE/$name" "$destination/$name"
                ;;
              "release upload")
                shift 3
                printf '%s\n' "$@" > "$UPLOAD_LOG"
                ;;
              *) exit 98 ;;
            esac
            """),
            encoding="utf-8",
        )
        gh.chmod(0o755)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def run_upload(self, existing: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(self.script), "alpha-v1.0.0", str(self.pdf), str(self.checksums)],
            env={
                **os.environ,
                "PATH": f"{self.bin}:{os.environ['PATH']}",
                "EXISTING_ASSETS": existing,
                "ASSET_STORE": str(self.store),
                "UPLOAD_LOG": str(self.root / "uploads"),
            },
            capture_output=True,
            text=True,
            check=False,
        )

    def test_matching_existing_asset_is_kept_and_only_missing_asset_is_uploaded(
        self,
    ) -> None:
        shutil.copy2(self.pdf, self.store / self.pdf.name)

        result = self.run_upload(self.pdf.name + "\n")

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Existing release asset matches", result.stdout)
        self.assertEqual(
            (self.root / "uploads").read_text(encoding="utf-8").splitlines(),
            [str(self.checksums)],
        )

    def test_conflicting_existing_asset_stops_before_upload(self) -> None:
        (self.store / self.pdf.name).write_bytes(b"different")

        result = self.run_upload(self.pdf.name + "\n")

        self.assertEqual(result.returncode, 1)
        self.assertIn("different content", result.stderr)
        self.assertFalse((self.root / "uploads").exists())


if __name__ == "__main__":
    unittest.main()
