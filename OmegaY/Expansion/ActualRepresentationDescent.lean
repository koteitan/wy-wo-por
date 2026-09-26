/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRepresentationDescent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.DynamicsRepresentationRank
import OmegaY.Expansion.ActualInitialReservoir
import OmegaY.Expansion.ActualSpliceRepresentation

/-!
# Actual representation descent for every nonempty legal input

The nontrivial branch below is recovered from an actual successful build
and run. It identifies both mountains with the prepared execution, leaving
no caller-supplied mountain or source-geometry correspondence. Deletion and
positive-copy cases both return an actual representation whose every label
is strictly below the old last label, in the same supported dimension.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

/-- Exhaustive nontrivial input preparation, with deterministic equality
of the built input and actual expanded output. -/
theorem nontrivial_representation_preparation
    {input : List Nat} {initial result : Mountain} {copies : Nat}
    (hBuild : Canonical.build input = .ok initial) (hNonempty : input ≠ [])
    (hRun : expandDiagram input copies = .ok result)
    (hNontrivial : ¬(input.getLast? = some 1 ∨ copies = 0)) :
    ∃ (middle : List Nat) (last : Nat) (hLast : 1 < last)
      (p : Preparation (1 :: middle) last),
      input = (1 :: middle) ++ [last] ∧ initial = p.initial ∧
      result = p.spliceMountain hLast copies ∧ 0 < copies := by
  have hLegal := build_success_legal hBuild
  rcases hLegal with hEmpty | ⟨rest, hInput, hPositive⟩
  · exact (hNonempty hEmpty).elim
  · subst input
    rcases List.eq_nil_or_concat' rest with hEmpty | ⟨middle, last, hRest⟩
    · subst rest
      exact (hNontrivial (Or.inl (by rfl))).elim
    · subst rest
      have hLastPositive : 0 < last := hPositive last (by simp)
      have hLastNe : last ≠ 1 := by
        intro he
        apply hNontrivial
        left
        change ((1 :: middle) ++ [last]).getLast? = some 1
        rw [List.getLast?_append]
        simp only [List.getLast?_singleton]
        exact congrArg some he
      have hLast : 1 < last := by omega
      have hCopies : 0 < copies := by omega
      obtain ⟨p⟩ := preparation_total middle last
        (fun value hv => hPositive value (by simp [hv])) hLast
      refine ⟨middle, last, hLast, p, rfl, ?_, ?_, hCopies⟩
      · exact Except.ok.inj (hBuild.symm.trans p.initial_build)
      · exact Except.ok.inj (hRun.symm.trans (p.expandDiagram_eq_spliceMountain_all hLast copies))

/-- All executable branches are closed. The preparation, complete finite
edge classification, initial reservoirs and finite reflections are proved
internally; no well-foundedness or representation-descent oracle is an
input. The chosen dimension is preserved by the actual dynamics. -/
theorem actual_representation_descent : Dynamics.ActualRepresentationDescent := by
  intro input initial result copies D hBuild hNonempty hDimension hRun old
  by_cases hTrivial : input.getLast? = some 1 ∨ copies = 0
  · exact expandDiagram_trivial_representation_descent hBuild hNonempty hRun hTrivial old
  · obtain ⟨middle, last, hLast, p, hInput, hInitial, _hResult, hCopies⟩ :=
      nontrivial_representation_preparation hBuild hNonempty hRun hTrivial
    subst input
    subst initial
    obtain ⟨g⟩ := p.root_geometry hLast
    exact g.represent_actual_expansion hLast hDimension old hCopies hRun

end OmegaY.Expansion

#print axioms OmegaY.Expansion.nontrivial_representation_preparation
#print axioms OmegaY.Expansion.actual_representation_descent
