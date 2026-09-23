/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/TotalRawGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BlocksRawGeometry
import OmegaY.Expansion.TotalEquations
import OmegaY.Expansion.TotalBottomLegs

/-!
# Raw row geometry for every actual weak omega-Y expansion

The real block execution establishes the stored-parent row equation before
the final column is removed. Prefix preservation then transfers it to the
returned mountain. Empty, terminal-one, and zero-copy inputs use the actual
canonical build and truncation. This does not identify stored parents with
the numerical ancestor search in the returned graph.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem Preparation.expandDiagram_raw_geometry {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : Mountain} (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    MountainRawGeometry result := by
  obtain ⟨full, hBlocks, _, hRaw⟩ := p.blocks_raw_geometry hLast copies
  have hActual := p.expandDiagram_of_blocks hLast hCopies hBlocks
  have he : full.pop = result := Except.ok.inj (hActual.symm.trans hRun)
  exact he ▸ hRaw.pop

/-- The full actual output has raw geometry for every legal input and every
finite copy count, without an output-normality or output-parent hypothesis. -/
theorem expandDiagram_raw_geometry {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result) :
    MountainRawGeometry result := by
  by_cases hTrivial : values.isEmpty ∨ values.getLast? = some 1 ∨ copies = 0
  · obtain ⟨initial, hBuild, _, _⟩ := build_total hLegal
    have hActual : expandDiagram values copies = .ok initial.pop := by
      simp only [List.isEmpty_iff] at hTrivial
      simp [expandDiagram, hBuild, Except.mapError, hTrivial]
    have he : initial.pop = result := Except.ok.inj (hActual.symm.trans hRun)
    exact he ▸ (mountainRawGeometry_of_normal (build_normal_of_success hBuild)).pop
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
        exact p.expandDiagram_raw_geometry hLast hCopies hRun

/-- A totality certificate with the now unconditional raw row law. -/
theorem expandDiagram_total_with_raw_geometry {values : List Nat}
    (hLegal : Legal values) (copies : Nat) :
    ∃ result, expandDiagram values copies = .ok result ∧ MountainValid result ∧
      MountainSums result ∧ MountainTops result ∧ BottomLegs result ∧
      MountainRawGeometry result := by
  obtain ⟨result, hRun, hValid, hSums, hTops⟩ :=
    expandDiagram_total_with_equations hLegal copies
  exact ⟨result, hRun, hValid, hSums, hTops,
    expandDiagram_bottom_legs hLegal hRun, expandDiagram_raw_geometry hLegal hRun⟩

/-- Every real stored-parent edge in the returned graph has a real, smaller
valued parent and the exact ordinal row equation. This is an internal edge
statement; it is not a decreasing measure for successive expansions. -/
theorem expandDiagram_real_raw_parent {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result)
    {u upper : (Frame.ofMountain result).Node} (hReal : Frame.Real u)
    (hUpper : (Frame.ofMountain result).upper u = some upper) :
    ∃ parent, (Frame.ofMountain result).rawParent u = some parent ∧
      Frame.Real parent ∧ parent.1.val < u.1.val ∧
      (Frame.ofMountain result).height parent ≤ (Frame.ofMountain result).height u ∧
      (Frame.ofMountain result).height upper =
        Row.B ((Frame.ofMountain result).height u) ((Frame.ofMountain result).height parent) ∧
      (Frame.ofMountain result).value parent < (Frame.ofMountain result).value u := by
  obtain ⟨actual, hActual, hValid⟩ := expandDiagram_total hLegal copies
  have he : actual = result := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  exact (expandDiagram_raw_geometry hLegal hRun).real_raw_parent hValid
    (expandDiagram_equations hLegal hRun).1 hReal hUpper

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.expandDiagram_raw_geometry
#print axioms OmegaY.Expansion.expandDiagram_raw_geometry
#print axioms OmegaY.Expansion.expandDiagram_total_with_raw_geometry
#print axioms OmegaY.Expansion.expandDiagram_real_raw_parent
