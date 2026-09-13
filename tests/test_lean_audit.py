"""Exercise the actual Lean audit against isolated compiled modules."""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
import unittest
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

    def audit(
        self,
        body: str,
        proof: str | None = None,
        *,
        in_root: bool = False,
        external: str | None = None,
    ) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            environment = {**os.environ, "LEAN_PATH": str(root)}
            module = root / "Textbooks/Fixture.lean"
            module.parent.mkdir()
            module.write_text("" if in_root else body)
            entry = root / "Textbooks.lean"
            entry.write_text("import Textbooks.Fixture\n" + (body if in_root else ""))
            sources = [module, entry]
            if external is not None:
                dependency = root / "External.lean"
                dependency.write_text(external)
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
                self.assertEqual(
                    compiled.returncode, 0, compiled.stdout + compiled.stderr
                )
            probe = root / "Audit.lean"
            source = (ROOT / "scripts/lean-proof-audit.lean").read_text()
            if proof:
                source += f"\nrun_cmd auditProof `{proof}\n"
            probe.write_text(source)
            return subprocess.run(
                [self.lean, str(probe)],
                cwd=root,
                env=environment,
                capture_output=True,
                text=True,
                timeout=60,
            )

    def test_checked_theorem_and_standard_classical_axioms_are_allowed(self) -> None:
        result = self.audit(
            "theorem result (p : Prop) : p ∨ ¬p := Classical.em p\n", "result"
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_registered_data_definition_is_not_a_proof(self) -> None:
        result = self.audit("def result : Nat := 0\n", "result")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("not a proof of a proposition", result.stdout)

    def test_missing_declaration_is_rejected(self) -> None:
        result = self.audit("", "missing")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("does not exist", result.stdout)

    def test_private_and_unused_axioms_are_rejected_without_registered_proofs(
        self,
    ) -> None:
        for in_root in (False, True):
            with self.subTest(in_root=in_root):
                result = self.audit(
                    "private axiom fabricated : False\n", in_root=in_root
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("repository-defined axiom", result.stdout)

    def test_sorry_in_an_unregistered_helper_is_rejected(self) -> None:
        for in_root in (False, True):
            with self.subTest(in_root=in_root):
                result = self.audit(
                    "theorem unfinished : False := by sorry\n", in_root=in_root
                )
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("forbidden axiom sorryAx", result.stdout)

    def test_transitive_external_axioms_are_rejected(self) -> None:
        result = self.audit(
            "theorem result : False := externalFact\n",
            "result",
            external="axiom externalFact : False\n",
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("forbidden axiom externalFact", result.stdout)

    def test_comment_and_string_mentions_are_not_escape_hatches(self) -> None:
        result = self.audit('-- sorry admit axiom\ndef note := "sorry admit axiom"\n')
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
