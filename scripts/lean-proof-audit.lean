import Lean
import Textbooks

/-! Validation tooling, copied into build/lean-links by check-proof-links.py.
This is not a mathematical textbook module. -/

open Lean Elab Command Meta

set_option autoImplicit false

private def auditAxioms (name : Name) : CommandElabM Unit := do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in (← collectAxioms name) do
    unless permitted.contains axiomName do
      throwError "{name} depends on forbidden axiom {axiomName}"

private def auditTextbookDeclarations : CommandElabM Unit := do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[index.toNat]!
    unless (`Textbooks).isPrefixOf moduleName do continue
    if info matches .axiomInfo _ then
      throwError "repository-defined axiom is forbidden: {name}"
    auditAxioms name

private def auditProof (name : Name) : CommandElabM Unit := do
  let some info := (← getEnv).find? name
    | throwError "registered proof declaration does not exist: {name}"
  if info.isUnsafe then
    throwError "registered proof is unsafe: {name}"
  unless (← liftTermElabM <| isProp info.type) do
    throwError "registered declaration is not a proof of a proposition: {name}"
  auditAxioms name

run_cmd auditTextbookDeclarations
