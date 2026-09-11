/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasCausal
import Lean.Meta
import Lean.Util.CollectAxioms

open Lean Meta

private def matchesCanonical (certificateName statementName : Name) : MetaM Bool := do
  let certificate ← mkConstWithFreshMVarLevels certificateName
  let statement ← mkConstWithFreshMVarLevels statementName
  let certificateType ← inferType certificate
  forallTelescopeReducing (← inferType statement) fun parameters resultType => do
    unless ← isDefEq resultType (mkSort .zero) do return false
    let proposition := mkAppN statement parameters
    let canonicalType ← mkForallFVars parameters proposition
    isDefEq certificateType canonicalType

private def checkProofs : CoreM (Array String × Nat) := do
  let env ← getEnv
  let mut errors := #[]
  let mut count := 0
  for (name, _) in env.constants.toList do
    let some index := env.getModuleIdxFor? name | continue
    let moduleName := env.header.moduleNames[index]!
    unless moduleName == `CapacityAtlasCausal || (`CapacityAtlasCausal).isPrefixOf moduleName do
      continue
    count := count + 1
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun axiomName ↦
      !(#[``propext, ``Quot.sound, ``Classical.choice]).contains axiomName
    unless unexpected.isEmpty do
      errors := errors.push s!"{name}: unexpected axioms {unexpected.toList}"
  if count == 0 then errors := errors.push "No proof declarations were loaded"
  let certificateName := `CapacityAtlasCausal.capacityCertificate
  let statementName := `CapacityAtlas.Channel.causalStateCapacityStatement
  let controlName := `CapacityAtlasCausal.exists_capacityAchieving_strategy
  if !env.contains certificateName then
    errors := errors.push "The registered capacity certificate is missing"
  else if !env.contains statementName then
    errors := errors.push "The canonical Atlas proposition is missing"
  else if !env.contains controlName then
    errors := errors.push "The optimizer theorem used for the type-mismatch control is missing"
  else
    unless ← (matchesCanonical certificateName statementName).run' do
      errors := errors.push "The certificate type does not match the canonical Atlas proposition"
    if ← (matchesCanonical controlName statementName).run' then
      errors := errors.push "The type-mismatch control accepted a different proposition"
  return (errors, count)

def main : IO UInt32 := do
  unsafe Lean.enableInitializersExecution
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `CapacityAtlasCausal }] {} (loadExts := true)
  let context : Core.Context := { fileName := "", fileMap := default }
  let state : Core.State := { env }
  let ((errors, count), _) ← checkProofs.toIO context state
  for error in errors do IO.eprintln error
  IO.println s!"Audited {count} declarations and canonical proposition correspondence; {errors.size} errors"
  return if errors.isEmpty then 0 else 1
