import GapEntropy
import Lean.Util.CollectAxioms

/-!
# Recursive axiom audit

Building this module checks every declaration in the `GapEntropy` namespace,
including `GapEntropy.PolicyRepresentations` and private declarations after restoring their user names.
Elaboration fails if any declaration depends on `sorryAx` or on an axiom outside
Lean's standard classical base `propext`, `Classical.choice`, `Quot.sound`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.toList do
    let visibleName := (privateToUserName? name).getD name
    if (`GapEntropy).isPrefixOf visibleName then
      declarations := declarations + 1
      if info.isTheorem then
        theorems := theorems + 1
      let axioms ← collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Axiom audit passed: {declarations} declarations ({theorems} theorems) \
    depend only on propext, Classical.choice, and Quot.sound."
