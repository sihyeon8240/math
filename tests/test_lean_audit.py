"""Exercise the actual Lean audit against isolated compiled modules."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

from scripts.lean_source import escape_hatch_lines

ROOT = Path(__file__).resolve().parent.parent


class LeanSourceTests(unittest.TestCase):
    def test_anonymous_examples_and_private_axioms_are_detected(self) -> None:
        self.assertEqual(escape_hatch_lines("example : False := by sorry\n"), [1])
        self.assertEqual(escape_hatch_lines("private axiom fabricated : False\n"), [1])
        self.assertEqual(escape_hatch_lines("example : False := by\n  admit\n"), [2])

    def test_nested_comments_strings_and_quoted_identifiers_are_ignored(self) -> None:
        self.assertEqual(
            escape_hatch_lines(
                "/- outer /- sorry -/ axiom -/\n-- admit\n"
                'def note := "sorry admit axiom"\ndef «sorry» := 0\n'
            ),
            [],
        )


@dataclass(frozen=True)
class AuditCase:
    name: str
    body: str
    proof: str | None = None
    diagnostic: str | None = None
    in_root: bool = False
    external: str | None = None


@unittest.skipUnless(shutil.which("lake"), "the pinned Lean toolchain is required")
class LeanAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        result = subprocess.run(
            ["lake", "env", "lean", "--print-prefix"],
            cwd=ROOT / "lean",
            capture_output=True,
            text=True,
            check=True,
            timeout=60,
        )
        cls.lean = str(Path(result.stdout.strip()) / "bin/lean")

    def audit(self, case: AuditCase) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            environment = {**os.environ, "LEAN_PATH": str(root)}
            module = root / "Textbooks/Fixture.lean"
            module.parent.mkdir()
            module.write_text("" if case.in_root else case.body)
            entry = root / "Textbooks.lean"
            entry.write_text(
                "import Textbooks.Fixture\n" + (case.body if case.in_root else "")
            )
            sources = [module, entry]
            if case.external is not None:
                dependency = root / "External.lean"
                dependency.write_text(case.external)
                module.write_text("import External\n" + module.read_text())
                sources.insert(0, dependency)
            for source in sources:
                compiled = subprocess.run(
                    [self.lean, "-o", str(source.with_suffix(".olean")), str(source)],
                    cwd=root,
                    env=environment,
                    capture_output=True,
                    text=True,
                    timeout=60,
                )
                if compiled.returncode != 0:
                    raise AssertionError(compiled.stdout + compiled.stderr)
            probe = root / "Audit.lean"
            source = (ROOT / "scripts/lean-proof-audit.lean").read_text()
            if case.proof:
                source += f"\nrun_cmd auditProof `{case.proof}\n"
            probe.write_text(source)
            return subprocess.run(
                [self.lean, str(probe)],
                cwd=root,
                env=environment,
                capture_output=True,
                text=True,
                timeout=60,
            )

    def test_isolated_audit_cases(self) -> None:
        cases = [
            AuditCase(
                "standard classical axioms",
                "theorem result (p : Prop) : p ∨ ¬p := Classical.em p\n",
                proof="result",
            ),
            AuditCase(
                "registered data definition",
                "def result : Nat := 0\n",
                proof="result",
                diagnostic="not a proof of a proposition",
            ),
            AuditCase(
                "missing declaration",
                "",
                proof="missing",
                diagnostic="does not exist",
            ),
            AuditCase(
                "transitive external axiom",
                "theorem result : False := externalFact\n",
                proof="result",
                external="axiom externalFact : False\n",
                diagnostic="forbidden axiom externalFact",
            ),
            AuditCase(
                "private unfinished helper",
                "private theorem unfinished : False := by sorry\n",
                diagnostic="forbidden axiom sorryAx",
            ),
            AuditCase(
                "unused external axiom",
                "theorem result : True := True.intro\n",
                proof="result",
                external="axiom unusedExternalFact : False\n",
            ),
            AuditCase(
                "comments and strings",
                '-- sorry admit axiom\ndef note := "sorry admit axiom"\n',
            ),
        ]
        for in_root in (False, True):
            cases.extend(
                [
                    AuditCase(
                        "private unused axiom",
                        "private axiom fabricated : False\n",
                        diagnostic="repository-defined axiom",
                        in_root=in_root,
                    ),
                    AuditCase(
                        "unregistered unfinished helper",
                        "theorem unfinished : False := by sorry\n",
                        diagnostic="forbidden axiom sorryAx",
                        in_root=in_root,
                    ),
                ]
            )

        # Workers launch isolated Lean processes; assertions and reporting stay serial.
        workers = min(4, os.cpu_count() or 1)
        with ThreadPoolExecutor(max_workers=workers) as executor:
            pending = [(case, executor.submit(self.audit, case)) for case in cases]
            for case, future in pending:
                with self.subTest(case=case.name, in_root=case.in_root):
                    result = future.result()
                    diagnostic = result.stdout + result.stderr
                    if case.diagnostic is None:
                        self.assertEqual(result.returncode, 0, diagnostic)
                    else:
                        self.assertNotEqual(result.returncode, 0, diagnostic)
                        self.assertIn(case.diagnostic, diagnostic)


if __name__ == "__main__":
    unittest.main()
