import MagHK
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0

/-!
Audit every declaration originating in this project's imported modules,
including private declarations and declarations outside the MagHK namespace.
Passing this audit
means that the checked statements have no additional axioms. It does not
remove hypotheses from the statements, or assert coverage of the manuscript.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut theoremCount : Nat := 0
  let mut definitionCount : Nat := 0
  let mut failures : Array (Name × Array Name) := #[]
  for (name, info) in env.constants.toList do
    let projectDeclaration := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!.getRoot == `MagHK
      | none => name.getRoot == `MagHK
    if projectDeclaration then
      if !name.isInternalDetail then
        match info with
        | .thmInfo _ => theoremCount := theoremCount + 1
        | .defnInfo _ => definitionCount := definitionCount + 1
        | _ => pure ()
      let dependencies ← liftCoreM (Lean.collectAxioms name)
      let unexpected := dependencies.filter fun ax => !allowed.contains ax
      if !unexpected.isEmpty then
        failures := failures.push (name, unexpected)
  if theoremCount == 0 then
    throwError "No project theorems were imported"
  unless failures.isEmpty do
    throwError "Unexpected axiom dependencies {failures}"
  let projectModules := env.header.moduleNames.filter fun n => n.getRoot == `MagHK
  logInfo m!"AUDIT_MODULES {String.intercalate "," (projectModules.toList.map Name.toString)}"
  logInfo m!"AUDIT PASSED. {theoremCount} theorems and {definitionCount} definitions."
  logInfo "Only propext, Classical.choice and Quot.sound are allowed."
  logInfo "Explicit theorem hypotheses are not discharged by this audit."
