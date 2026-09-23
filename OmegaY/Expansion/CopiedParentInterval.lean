/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CopiedParentInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ContourAdjacent
import OmegaY.Expansion.ShiftedEdgeInterval

/-!
# Strict-below selection in an actual copied contour interval

The source pair is consecutive and has no intervening marker. Actual output
adjacency, not a power-step guess, supplies the upper barrier. Thus both the
selected reference and its lifted row follow from the real copy execution.
-/

namespace OmegaY.Expansion.ColumnCopyData

open Canonical

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

theorem copyColumn_below_lifted_source_pair {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {oldLower oldUpper : Cell}
    (hLower : d.sources[sourceIndex]? = some oldLower)
    (hUpper : d.sources[sourceIndex + 1]? = some oldUpper)
    (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex + 1 →
      middle ∉ d.bucket.map Ref.index)
    {oldCeiling : Row} (hLow : oldLower.row < oldCeiling) (hHigh : oldCeiling ≤ oldUpper.row) :
    ∃ (index : Nat) (parent : Cell),
      below (mountain.push column) mountain.size
        (Row.lift (d.marker_data marker hm).current.row
          (d.marker_data marker hm).targetCell.row oldCeiling) = .ok ⟨mountain.size, index⟩ ∧
      column[index]? = some parent ∧
      Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok parent ∧
      parent.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldLower.row := by
  obtain ⟨position, lower, upper, hLo, hHi, hLoRow, hHiRow⟩ :=
    d.copyColumn_source_adjacent_of_no_between hParentPower hParentLow hNoPremature
      hRun hm hLower hUpper hAfter hNoBetween
  obtain ⟨output, hOutput, _, _, _, hValid⟩ := d.copyColumn_valid
  have he : output = column := Except.ok.inj (hOutput.symm.trans hRun)
  subst output
  have hRootLow : (d.marker_data marker hm).current.row ≤ oldLower.row :=
    (d.source_valid.rows_strict _ _ _ _ (d.marker_data marker hm).current_at hLower hAfter).le
  have hLiftLow : lower.row < Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row oldCeiling := by
    rw [hLoRow]
    exact Row.lift_strictMono hRootLow hLow
  have hLiftHigh : Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row oldCeiling ≤ upper.row := by
    rw [hHiRow]
    exact Row.lift_monotone (hRootLow.trans hLow.le) hHigh
  have hColumn : (mountain.push column)[mountain.size]? = some column := by simp
  exact ⟨position, lower, below_eq_of_adjacent hValid hColumn hLo hHi hLiftLow hLiftHigh,
    hLo, cellAt_ok_iff.mpr ⟨column, hColumn, hLo⟩, hLoRow⟩

/-- Appending further actual columns preserves the selected source column
and hence the exact strict-below result. This is the use site needed when
the child column is copied later in the same block. -/
theorem copyColumn_below_lifted_source_pair_preserved {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {later : Mountain} (hPreserve : PreservesColumns (mountain.push column) later)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {oldLower oldUpper : Cell}
    (hLower : d.sources[sourceIndex]? = some oldLower)
    (hUpper : d.sources[sourceIndex + 1]? = some oldUpper)
    (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex + 1 →
      middle ∉ d.bucket.map Ref.index)
    {oldCeiling : Row} (hLow : oldLower.row < oldCeiling) (hHigh : oldCeiling ≤ oldUpper.row) :
    ∃ (index : Nat) (parent : Cell),
      below later mountain.size (Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldCeiling) = .ok ⟨mountain.size, index⟩ ∧
      Canonical.cellAt later ⟨mountain.size, index⟩ = .ok parent ∧
      parent.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldLower.row := by
  obtain ⟨index, parent, hBelow, hRead, hCell, hRow⟩ :=
    d.copyColumn_below_lifted_source_pair hParentPower hParentLow hNoPremature
      hRun hm hLower hUpper hAfter hNoBetween hLow hHigh
  have hColumn := hPreserve mountain.size (by simp)
  have hOldColumn : (mountain.push column)[mountain.size]? = some column := by simp
  have hNewColumn : later[mountain.size]? = some column := hColumn.trans hOldColumn
  refine ⟨index, parent, ?_, cellAt_ok_iff.mpr ⟨column, hNewColumn, hRead⟩, hRow⟩
  exact (hPreserve.below (by simp) _).trans hBelow

#print axioms copyColumn_below_lifted_source_pair
#print axioms copyColumn_below_lifted_source_pair_preserved

end OmegaY.Expansion.ColumnCopyData
