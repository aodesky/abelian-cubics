import Cubic
import CubicTargets
import Lean.Util.CollectAxioms

/-!
Check the transitive axioms of declarations in `Cubic` and `CubicTargets`, including
statement definitions. Only Lean's standard logical axioms are allowed.
Share Lean's collector state across roots so common mathlib dependencies are
traversed once. Every project root is still visited; the cumulative axiom set
is checked after each visit.
Run with `lake env lean Audit.lean` after `lake build`.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  let mut axiomState : CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    if (`Cubic).isPrefixOf name || (`CubicTargets).isPrefixOf name then
      count := count + 1
      let (_, nextState) := ((CollectAxioms.collect name).run env).run axiomState
      axiomState := nextState
      for axiomName in axiomState.axioms do
        unless allowed.contains axiomName do
          throwError "{name} depends on disallowed axiom {axiomName}"
  if count == 0 then
    throwError "No Cubic declarations found; check the root imports."
  logInfo m!"Axiom audit passed for {count} project declarations (including statements)."
