/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FiniteDegree.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.TotalRowBound

/-! One finite exponent dimension bounds every row in every finite-copy
output of a fixed input. Applying this bound to the newly rebuilt mountain
in a later expansion still requires the canonical-reconstruction theorem. -/

namespace OmegaY.Row

theorem jump_zero_monotone : Monotone (fun row : Row => jump 0 row) := by
  intro a b h
  exact (jump_le_between (zero_le a) h (le_refl (jump 0 b))).1

theorem coeff_zero_above_bound {row height : Row} (h : row ≤ height) {degree : Nat}
    (hDegree : jump 0 height ≤ degree) : coeff row degree = 0 := by
  have hJump := jump_zero_monotone h
  have hCoeff := coeff_eq_of_jump_le hJump hDegree
  simpa only [coeff_zero] using hCoeff.symm

end OmegaY.Row

namespace OmegaY.Expansion

open Canonical

def rowCeiling (mountain : Mountain) : Row :=
  (mountain.toList.flatMap (fun column => column.toList.map Cell.row)).foldr max 0

private theorem mem_le_foldr_max {row : Row} {rows : List Row} (h : row ∈ rows) :
    row ≤ rows.foldr max 0 := by
  induction rows with
  | nil => cases h
  | cons head tail ih =>
    rcases List.mem_cons.mp h with rfl | hTail
    · exact le_max_left _ _
    · exact le_trans (ih hTail) (le_max_right _ _)

theorem rowCeiling_bound (mountain : Mountain) : MountainRowsBound mountain (rowCeiling mountain) := by
  intro ref cell hCell
  obtain ⟨column, hColumn, hRead⟩ := cellAt_ok_iff.mp hCell
  apply mem_le_foldr_max
  apply List.mem_flatMap.mpr
  refine ⟨column, ?_, List.mem_map.mpr ⟨cell, ?_, rfl⟩⟩
  · exact List.mem_iff_getElem?.mpr ⟨ref.column, by simpa only [Array.getElem?_toList] using hColumn⟩
  · exact List.mem_iff_getElem?.mpr ⟨ref.index, by simpa only [Array.getElem?_toList] using hRead⟩

def exponentBound (mountain : Mountain) : Nat := Row.jump 0 (rowCeiling mountain)

theorem expandDiagram_fixed_exponent_bound {values : List Nat} {initial : Mountain}
    (hBuild : Canonical.build values = .ok initial) {copies : Nat} {result : Mountain}
    (hRun : expandDiagram values copies = .ok result) :
    ∀ ref cell, Canonical.cellAt result ref = .ok cell →
      Row.jump 0 cell.row ≤ exponentBound initial ∧
      ∀ degree, exponentBound initial ≤ degree → Row.coeff cell.row degree = 0 := by
  have hBound := expandDiagram_rows_bound hBuild (rowCeiling_bound initial) hRun
  intro ref cell hCell
  have hRow := hBound ref cell hCell
  exact ⟨Row.jump_zero_monotone hRow,
    fun _ hDegree => Row.coeff_zero_above_bound hRow hDegree⟩

theorem expandDiagram_pair_jump_bound {values : List Nat} {initial : Mountain}
    (hBuild : Canonical.build values = .ok initial) {copies : Nat} {result : Mountain}
    (hRun : expandDiagram values copies = .ok result)
    {leftRef rightRef : Ref} {leftCell rightCell : Cell}
    (hLeft : Canonical.cellAt result leftRef = .ok leftCell)
    (hRight : Canonical.cellAt result rightRef = .ok rightCell) :
    Row.jump leftCell.row rightCell.row ≤ exponentBound initial := by
  have hLeftBound := (expandDiagram_fixed_exponent_bound hBuild hRun leftRef leftCell hLeft).1
  have hRightBound := (expandDiagram_fixed_exponent_bound hBuild hRun rightRef rightCell hRight).1
  have hTriangle := Row.jump_triangle leftCell.row 0 rightCell.row
  rw [Row.jump_comm leftCell.row 0] at hTriangle
  exact hTriangle.trans (max_le hLeftBound hRightBound)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_fixed_exponent_bound
#print axioms OmegaY.Expansion.expandDiagram_pair_jump_bound
