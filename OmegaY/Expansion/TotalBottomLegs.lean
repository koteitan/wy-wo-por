/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/TotalBottomLegs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BlocksBottomLegs
import OmegaY.Expansion.ReconstructionCertificate

/-! Exact bottom legs for every legal input and every finite copy count.
Consequently the conditional reconstruction bridge needs only the explicit
remaining parent-search/row geometry, not a separate bottom-leg premise. -/

namespace OmegaY.Expansion

open Canonical

theorem expandDiagram_bottom_legs {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result) :
    BottomLegs result := by
  by_cases hTrivial : values.isEmpty ∨ values.getLast? = some 1 ∨ copies = 0
  · obtain ⟨initial, hBuild, _, _⟩ := build_total hLegal
    have hActual : expandDiagram values copies = .ok initial.pop := by
      simp only [List.isEmpty_iff] at hTrivial
      simp [expandDiagram, hBuild, Except.mapError, hTrivial]
    have he : initial.pop = result := Except.ok.inj (hActual.symm.trans hRun)
    exact he ▸ (build_bottom_legs hBuild).pop
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
        exact p.expandDiagram_bottom_legs hLast hCopies hRun

/-- Numerical sums, tops, and exact bottom legs are already consequences
of actual expansion. Only `MountainParentGeometry` remains conditional. -/
theorem reconstruct_expansion_of_geometry {input : List Nat} (hLegal : Legal input)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram input copies = .ok mountain)
    (hGeometry : MountainParentGeometry mountain)
    {values : List Nat} (hValues : valuesOf mountain = .ok values) :
    Canonical.build values = .ok mountain :=
  reconstruct_expansion_of_parent_geometry hLegal hRun
    (expandDiagram_bottom_legs hLegal hRun) hGeometry hValues

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_bottom_legs
#print axioms OmegaY.Expansion.reconstruct_expansion_of_geometry
