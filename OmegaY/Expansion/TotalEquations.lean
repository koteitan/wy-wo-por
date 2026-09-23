/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/TotalEquations.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.Totality
import OmegaY.Expansion.BlockEquations

/-! Every actual expanded graph has the proved numerical equations and
value-one tops. These are necessary reconstruction certificates; they do
not assert that its stored parent is the canonical numerical parent. -/

namespace OmegaY.Expansion

open Canonical

theorem expandDiagram_equations {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result) :
    MountainSums result ∧ MountainTops result := by
  by_cases hTrivial : values.isEmpty ∨ values.getLast? = some 1 ∨ copies = 0
  · obtain ⟨initial, hBuild, hValid, hTops⟩ := build_total hLegal
    have hActual : expandDiagram values copies = .ok initial.pop := by
      simp only [List.isEmpty_iff] at hTrivial
      simp [expandDiagram, hBuild, Except.mapError, hTrivial]
    have he : initial.pop = result := Except.ok.inj (hActual.symm.trans hRun)
    subst result
    exact ⟨(build_mountain_sums hBuild).pop hValid, MountainTops.pop hTops⟩
  · rcases hLegal with rfl | ⟨rest, rfl, hPositive⟩
    · simp at hTrivial
    · rcases List.eq_nil_or_concat' rest with rfl | ⟨middle, last, rfl⟩
      · simp at hTrivial
      · have hLastPositive : 0 < last := hPositive last (by simp)
        have hLastNe : last ≠ 1 := by
          intro hLast
          apply hTrivial
          right; left
          change ((1 :: middle) ++ [last]).getLast? = some 1
          rw [List.getLast?_append]
          simp [hLast]
        have hLast : 1 < last := by omega
        have hCopies : 0 < copies := by
          by_contra h
          apply hTrivial
          right; right
          omega
        obtain ⟨p⟩ := preparation_total middle last
          (fun value hv => hPositive value (by simp [hv])) hLast
        exact p.expandDiagram_equations hLast hCopies hRun

theorem expandDiagram_total_with_equations {values : List Nat}
    (hLegal : Legal values) (copies : Nat) :
    ∃ result, expandDiagram values copies = .ok result ∧ MountainValid result ∧
      MountainSums result ∧ MountainTops result := by
  obtain ⟨result, hRun, hValid⟩ := expandDiagram_total hLegal copies
  exact ⟨result, hRun, hValid, expandDiagram_equations hLegal hRun⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_equations
#print axioms OmegaY.Expansion.expandDiagram_total_with_equations
