/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ReconstructionCertificate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.TotalEquations
import OmegaY.Canonical.Reconstruction

/-! An explicit remaining interface for reconstruction. Numerical sums and
tops are supplied by actual expansion. This file does not prove the parent
geometry for actual marker/contour nodes: both the exact B row and the
actual first-smaller search are fields still to be established there. -/

namespace OmegaY.Expansion

open Canonical Geometry

def ColumnParentGeometry (mountain : Mountain) (c : Nat) (column : Column) : Prop :=
  ∀ (index : Nat) (lower upper : Cell), column[index]? = some lower →
    column[index + 1]? = some upper → 0 < index →
    ∃ ref parent, upper.left = some ref ∧ Canonical.cellAt mountain ref = .ok parent ∧
      findParent mountain ⟨c, index⟩ = .ok ref ∧ upper.row = Row.B lower.row parent.row

def MountainParentGeometry (mountain : Mountain) : Prop :=
  ∀ c (hc : c < mountain.size), ColumnParentGeometry mountain c mountain[c]

theorem columnSteps_of_sums_geometry {mountain : Mountain} {c : Nat} {column : Column}
    (hValid : ColumnValid mountain c column)
    (hSums : column.toList.IsChain (AdjacentSum mountain))
    (hGeometry : ColumnParentGeometry mountain c column) : ColumnSteps mountain c column := by
  intro index lower upper hLower hUpper hIndex
  obtain ⟨ref, parent, hLeft, hParent, hFind, hRow⟩ := hGeometry index lower upper hLower hUpper hIndex
  have hi := (Array.getElem?_eq_some_iff.mp hLower).1
  have hj := (Array.getElem?_eq_some_iff.mp hUpper).1
  have hLowerEq : column.toList[index] = lower := by
    simpa only [Array.getElem_toList, Array.getElem?_eq_getElem hi, Option.some.injEq] using hLower
  have hUpperEq : column.toList[index + 1] = upper := by
    simpa only [Array.getElem_toList, Array.getElem?_eq_getElem hj, Option.some.injEq] using hUpper
  have hSum := (List.isChain_iff_getElem.mp hSums) index
    (by simpa only [Array.length_toList] using hj)
  rw [hLowerEq, hUpperEq] at hSum
  have hReal : lower.row ≠ 0 := ne_of_gt
    (hValid.rows_strict 0 index phantom lower hValid.phantom hLower hIndex)
  obtain ⟨otherRef, otherParent, hOtherLeft, hOtherParent, hPositive, hValue⟩ := hSum hReal
  have hRefEq : otherRef = ref := Option.some.inj (hOtherLeft.symm.trans hLeft)
  subst otherRef
  have hParentEq : otherParent = parent := Except.ok.inj
    ((lookup_ok_iff.mpr (cellAt_ok_iff.mp hParent)).symm.trans hOtherParent).symm
  subst otherParent
  have hUpperPositive := hValid.real_positive (index + 1) upper hUpper (by omega)
  exact ⟨by omega, ref, parent, (hValid.stored_valid _ _ _ hUpper hLeft).1,
    hFind, hParent, hRow, by omega, hLeft⟩

theorem normal_of_sums_geometry {mountain : Mountain} (hValid : MountainValid mountain)
    (hSums : MountainSums mountain) (hTops : MountainTops mountain)
    (hGeometry : MountainParentGeometry mountain) : (Frame.ofMountain mountain).Normal :=
  normal_of_certificates hValid hTops
    (fun c hc => columnSteps_of_sums_geometry (hValid c hc) (hSums c hc) (hGeometry c hc))

/-- This conditional bridge isolates the remaining actual-parent geometry
and bottom legs. Neither is claimed to follow from row bounds or sums. -/
theorem reconstruct_expansion_of_parent_geometry {input : List Nat} (hLegal : Legal input)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram input copies = .ok mountain)
    (hLegs : BottomLegs mountain) (hGeometry : MountainParentGeometry mountain)
    {values : List Nat} (hValues : valuesOf mountain = .ok values) :
    Canonical.build values = .ok mountain := by
  obtain ⟨actual, hActual, hValid⟩ := expandDiagram_total hLegal copies
  have he : actual = mountain := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  obtain ⟨hSums, hTops⟩ := expandDiagram_equations hLegal hRun
  exact build_reconstruct_of_valuesOf hValid
    (normal_of_sums_geometry hValid hSums hTops hGeometry) hLegs hValues

end OmegaY.Expansion

#print axioms OmegaY.Expansion.columnSteps_of_sums_geometry
#print axioms OmegaY.Expansion.reconstruct_expansion_of_parent_geometry
