/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Audit.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: the axiom audit also covers the theorems of `Por` (the model of this
repository), and the final theorems print their axioms.
-/
import OmegaY.All
import Lean.Util.CollectAxioms

-- These statements also check the final theorem types with no extra premises.
example : WellFounded OmegaY.Expansion.Dynamics.Step :=
  OmegaY.Expansion.omegaY_step_wellFounded

example : IsWellOrder OmegaY.Expansion.Dynamics.GeneratedExpr
    (fun a b => OmegaY.Expansion.Dynamics.Lex a.val b.val) :=
  OmegaY.Expansion.omegaY_generated_isWellOrder

example (root : OmegaY.Expansion.Dynamics.Expr) (copies : Nat → Nat) :
    ∃ n, (OmegaY.Expansion.Dynamics.trajectory root copies n).val = [] :=
  OmegaY.Expansion.omegaY_trajectory_terminates root copies

/-! Inspect the transitive axiom dependencies of every theorem declared by
this research project, including private theorems. Conditional theorem
premises are not axioms: they still require the separate semantic audit. -/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "OmegaY." || name.toString.startsWith "_private.OmegaY." ||
        name.toString.startsWith "Por." || name.toString.startsWith "_private.Por." then
      match info with
      | .axiomInfo _ => throwError "New research axiom declaration: {name}"
      | .thmInfo _ =>
        let axioms ← collectAxioms name
        let unexpected := axioms.filter fun ax => !allowed.contains ax
        unless unexpected.isEmpty do
          throwError "Unapproved axiom dependency in {name}: {unexpected}"
        count := count + 1
      | _ => pure ()
  logInfo m!"Audited {count} research theorems: only propext, Classical.choice and Quot.sound occur. No new axiom declaration."

#print axioms OmegaY.Expansion.omegaY_step_wellFounded
#print axioms OmegaY.Expansion.omegaY_generated_isWellOrder
#print axioms OmegaY.Expansion.omegaY_descendants_isWellOrder
#print axioms OmegaY.Expansion.omegaY_trajectory_terminates
