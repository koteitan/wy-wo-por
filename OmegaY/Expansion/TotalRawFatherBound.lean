/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/TotalRawFatherBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BlocksRawFatherBound
import OmegaY.Expansion.TotalRawGeometry

/-! Raw father-upper barriers for every actual legal-input expansion and
every finite copy count, including the final temporary-column removal. -/

namespace OmegaY.Expansion

open Canonical Geometry

theorem Preparation.expandDiagram_raw_father_bound {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : Mountain} (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    MountainRawFatherBound result := by
  obtain ⟨full, hBlocks, hReady, hBound⟩ := p.blocks_raw_father_bound hLast copies
  have hActual := p.expandDiagram_of_blocks hLast hCopies hBlocks
  have he : full.pop = result := Except.ok.inj (hActual.symm.trans hRun)
  exact he ▸ hBound.pop hReady.valid

theorem expandDiagram_raw_father_bound {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result) :
    MountainRawFatherBound result := by
  by_cases hTrivial : values.isEmpty ∨ values.getLast? = some 1 ∨ copies = 0
  · obtain ⟨initial, hBuild, hValid, _⟩ := build_total hLegal
    have hActual : expandDiagram values copies = .ok initial.pop := by
      simp only [List.isEmpty_iff] at hTrivial
      simp [expandDiagram, hBuild, Except.mapError, hTrivial]
    have he : initial.pop = result := Except.ok.inj (hActual.symm.trans hRun)
    exact he ▸ (mountainRawFatherBound_of_normal hValid
      (build_normal_of_success hBuild)).pop hValid
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
        exact p.expandDiagram_raw_father_bound hLast hCopies hRun

/-- The exact typed upper-stored parent relation satisfies raw D on the
actual returned mountain. It is not identified here with numerical P. -/
theorem expandDiagram_raw_father_upper_bound {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result) :
    (Frame.ofMountain result).RawFatherUpperBound :=
  (expandDiagram_raw_father_bound hLegal hRun).rawFatherUpperBound

theorem expandDiagram_total_with_raw_geometry_and_bound {values : List Nat}
    (hLegal : Legal values) (copies : Nat) :
    ∃ result, expandDiagram values copies = .ok result ∧ MountainValid result ∧
      MountainSums result ∧ MountainTops result ∧ BottomLegs result ∧
      MountainRawGeometry result ∧ MountainRawFatherBound result := by
  obtain ⟨result, hRun, hValid, hSums, hTops, hBottom, hRaw⟩ :=
    expandDiagram_total_with_raw_geometry hLegal copies
  exact ⟨result, hRun, hValid, hSums, hTops, hBottom, hRaw,
    expandDiagram_raw_father_bound hLegal hRun⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.expandDiagram_raw_father_bound
#print axioms OmegaY.Expansion.expandDiagram_raw_father_bound
#print axioms OmegaY.Expansion.expandDiagram_raw_father_upper_bound
#print axioms OmegaY.Expansion.expandDiagram_total_with_raw_geometry_and_bound
