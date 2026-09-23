/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/WellFounded.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRepresentationDescent
import Mathlib.Order.WellFounded

/-!
# Closed well-foundedness theorems for the actual omega-Y expansion

The step relation is the actual successful executable expansion on every
syntactically legal finite input, with the empty self-loop excluded. The
standard generated domain and each individual legal root's descendant
domain are lexicographically well-ordered. This does not assert that the
union of unrelated syntactically legal inputs is lexicographically
well-ordered.

The public endpoints below have no representation-descent, geometric,
key-transport, search-reconstruction, or well-foundedness hypothesis.
-/

namespace OmegaY.Expansion

/-- The actual nonempty-input expansion relation on all legal sequences
is well-founded, for arbitrary finite copy counts at each step. -/
theorem omegaY_step_wellFounded : WellFounded Dynamics.Step :=
  Dynamics.step_wellFounded_of_actual_representation_descent actual_representation_descent

/-- Standard seeds are `[1,n+2]`; their entire generated union carries
the actual finite-sequence lexicographic well-order. -/
theorem omegaY_generated_isWellOrder :
    IsWellOrder Dynamics.GeneratedExpr (fun a b => Dynamics.Lex a.val b.val) :=
  Dynamics.generated_isWellOrder omegaY_step_wellFounded

/-- Every legal starting expression, not just a standard seed, has a
lexicographically well-ordered domain of actual descendants. -/
theorem omegaY_descendants_isWellOrder (root : Dynamics.Expr) :
    IsWellOrder (Dynamics.Descendant root) (fun a b => Dynamics.Lex a.val b.val) :=
  Dynamics.every_legal_root_isWellOrder omegaY_step_wellFounded root

/-- This is the same relation stated directly with successful program
runs; the total-output choice in `Dynamics.next` adds no transitions. -/
theorem omegaY_executable_step_wellFounded :
    WellFounded (fun child parent : Dynamics.Expr => parent.val ≠ [] ∧
      ∃ copies, expand parent.val copies = .ok child.val) :=
  Subrelation.wf (fun {child parent} h => (Dynamics.step_iff_run child parent).mpr h)
    omegaY_step_wellFounded

theorem omegaY_no_infinite_step_chain (sequence : Nat → Dynamics.Expr) :
    ¬∀ n, Dynamics.Step (sequence (n + 1)) (sequence n) := by
  intro hSteps
  exact (wellFounded_iff_isEmpty_descending_chain.mp omegaY_step_wellFounded).false ⟨sequence, hSteps⟩

namespace Dynamics

/-- The user may choose a different finite count at every stage. -/
noncomputable def trajectory (root : Expr) (copies : Nat → Nat) : Nat → Expr
  | 0 => root
  | n + 1 => next (trajectory root copies n) (copies n)

@[simp] theorem trajectory_zero (root : Expr) (copies : Nat → Nat) :
    trajectory root copies 0 = root := rfl

@[simp] theorem trajectory_succ (root : Expr) (copies : Nat → Nat) (n : Nat) :
    trajectory root copies (n + 1) = next (trajectory root copies n) (copies n) := rfl

theorem trajectory_run (root : Expr) (copies : Nat → Nat) (n : Nat) :
    expand (trajectory root copies n).val (copies n) =
      .ok (trajectory root copies (n + 1)).val := next_run _ _

end Dynamics

/-- Every actual trajectory reaches the empty sequence after finitely
many expansions. The choices of finite copy counts are unrestricted. -/
theorem omegaY_trajectory_terminates (root : Dynamics.Expr) (copies : Nat → Nat) :
    ∃ n, (Dynamics.trajectory root copies n).val = [] := by
  by_contra hn
  apply omegaY_no_infinite_step_chain (Dynamics.trajectory root copies)
  intro n
  exact ⟨fun hEmpty => hn ⟨n, hEmpty⟩, copies n, rfl⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.omegaY_step_wellFounded
#print axioms OmegaY.Expansion.omegaY_generated_isWellOrder
#print axioms OmegaY.Expansion.omegaY_descendants_isWellOrder
#print axioms OmegaY.Expansion.omegaY_executable_step_wellFounded
#print axioms OmegaY.Expansion.omegaY_trajectory_terminates
