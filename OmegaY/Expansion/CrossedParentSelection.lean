/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CrossedParentSelection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ContourCapBarrier

/-!
# Parent selection beyond a reference cap

The reference cap need not bound the child's query. The actual copied
parent has the stronger barrier given by its source upper neighbour. A
query below the reference cap stays below that barrier; a query at or above
the reference cap is fixed by the lift. This also covers a marked source
upper, without inventing an output node at the cap.
-/

namespace OmegaY.Expansion.ColumnCopyData

open Canonical Geometry

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow hNoPremature

/-- The executable selector remains exact for every old ceiling up to the
source upper neighbour, including ceilings above the reference cap. -/
theorem copyColumn_below_lifted_crossed_pair {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {oldLower oldUpper : Cell}
    (hLower : d.sources[sourceIndex]? = some oldLower)
    (hUpper : d.sources[sourceIndex + 1]? = some oldUpper)
    (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
      middle ∉ d.bucket.map Ref.index) {degree : Nat}
    (hTargetCap : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row degree)
    (hUpperCap : Row.bump (d.marker_data marker hm).current.row degree ≤ oldUpper.row)
    {oldCeiling : Row} (hLow : oldLower.row < oldCeiling) (hHigh : oldCeiling ≤ oldUpper.row) :
    ∃ (index : Nat) (parent : Cell),
      below (mountain.push column) mountain.size
        (Row.lift (d.marker_data marker hm).current.row
          (d.marker_data marker hm).targetCell.row oldCeiling) = .ok ⟨mountain.size, index⟩ ∧
      column[index]? = some parent ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok parent ∧
      parent.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldLower.row := by
  let md := d.marker_data marker hm
  obtain ⟨index, parent, hParent, hRow, hBarrier⟩ :=
    d.copyColumn_crossed_cap_barrier hParentPower hParentLow hNoPremature
      hRun hm hLower hUpper hAfter hNoBetween (cap := oldUpper.row) le_rfl
  obtain ⟨otherColumn, hOther, _, _, _, hMountain⟩ := d.copyColumn_valid
  have he : otherColumn = column := Except.ok.inj (hOther.symm.trans hRun)
  subst otherColumn
  have hRootLow : md.current.row ≤ oldLower.row :=
    (d.source_valid.rows_strict _ _ _ _ md.current_at hLower hAfter).le
  have hQueryLow : parent.row < Row.lift md.current.row md.targetCell.row oldCeiling := by
    rw [hRow]
    exact Row.lift_strictMono hRootLow hLow
  have hQueryHigh : Row.lift md.current.row md.targetCell.row oldCeiling ≤ oldUpper.row := by
    by_cases hInside : oldCeiling < Row.bump md.current.row degree
    · exact (Row.lift_mem_interval md.target_lower hTargetCap
        (hRootLow.trans hLow.le) hInside).2.le.trans hUpperCap
    · rw [Row.lift_eq_of_ge_cap md.target_lower hTargetCap (le_of_not_gt hInside)]
      exact hHigh
  have hColumn : (mountain.push column)[mountain.size]? = some column := by simp
  have hValid : ColumnValid (mountain.push column) mountain.size column := by
    have h := hMountain mountain.size (by simp)
    simpa only [Array.getElem_push_eq] using h
  exact ⟨index, parent,
    below_eq_of_row_barrier hColumn hValid hParent hBarrier hQueryLow hQueryHigh,
    hParent, cellAt_ok_iff.mpr ⟨column, hColumn, hParent⟩, hRow⟩

/-- Later copied columns preserve the exact query and selected cell. -/
theorem copyColumn_below_lifted_crossed_pair_preserved {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {later : Mountain} (hPreserve : PreservesColumns (mountain.push column) later)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {oldLower oldUpper : Cell}
    (hLower : d.sources[sourceIndex]? = some oldLower)
    (hUpper : d.sources[sourceIndex + 1]? = some oldUpper)
    (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
      middle ∉ d.bucket.map Ref.index) {degree : Nat}
    (hTargetCap : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row degree)
    (hUpperCap : Row.bump (d.marker_data marker hm).current.row degree ≤ oldUpper.row)
    {oldCeiling : Row} (hLow : oldLower.row < oldCeiling) (hHigh : oldCeiling ≤ oldUpper.row) :
    ∃ (index : Nat) (parent : Cell),
      below later mountain.size (Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldCeiling) = .ok ⟨mountain.size, index⟩ ∧
      Canonical.cellAt later ⟨mountain.size, index⟩ = .ok parent ∧
      parent.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldLower.row := by
  obtain ⟨index, parent, hBelow, hRead, _, hRow⟩ :=
    d.copyColumn_below_lifted_crossed_pair hParentPower hParentLow hNoPremature
      hRun hm hLower hUpper hAfter hNoBetween hTargetCap hUpperCap hLow hHigh
  have hOldColumn : (mountain.push column)[mountain.size]? = some column := by simp
  have hNewColumn : later[mountain.size]? = some column :=
    (hPreserve mountain.size (by simp)).trans hOldColumn
  exact ⟨index, parent, (hPreserve.below (by simp) _).trans hBelow,
    cellAt_ok_iff.mpr ⟨column, hNewColumn, hRead⟩, hRow⟩

end OmegaY.Expansion.ColumnCopyData

#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_lifted_crossed_pair
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_lifted_crossed_pair_preserved
