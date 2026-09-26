/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/AdjacentEffectiveSources.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveCopy
import OmegaY.Expansion.SeamSourceAt
import OmegaY.Expansion.MarkerContourGeometry

/-! Exact inverse source certificates for ordinary output adjacencies.
The lower endpoint is the effective source occurrence, including a raised
marker at the top of its fill and a cross-segment physical upper marker. -/

namespace OmegaY.Expansion
open Canonical

structure EffectiveAdjacentSource {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (column : Column) (index : Nat) (lower : Cell) where
  sourceIndex : Nat
  sourceLower : Cell
  sourceUpper : Cell
  read : EffectiveCopyRead d sourceIndex sourceLower column
  upper_at : d.sources[sourceIndex + 1]? = some sourceUpper
  output_index : read.outputIndex = index
  output_cell : read.outputCell = lower

namespace ColumnCopyData
variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

theorem marker_effective_adjacent_source {column : Column} {index : Nat} {lower : Cell}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    (hRead : column[index]? = some lower) {marker : Ref} (hm : marker ∈ d.bucket)
    (hRow : lower.row = (d.marker_data marker hm).targetCell.row) :
    Nonempty (EffectiveAdjacentSource d column index lower) := by
  let md := d.marker_data marker hm
  exact ⟨{
    sourceIndex := marker.index, sourceLower := md.current, sourceUpper := md.upper,
    read := {
      source_at := md.current_at, copy_run := hRun,
      marker := marker, marker_mem := hm, marker_before := le_rfl,
      no_between := by intros; omega, source_lower := le_rfl,
      outputIndex := index, outputCell := lower, output_at := hRead,
      output_row := by simpa only [md, Row.lift_at_root] using hRow },
    upper_at := md.upper_at, output_index := rfl, output_cell := rfl }⟩

end ColumnCopyData

section Pair
variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
  {index : Nat} {lower upper : Cell}
  (pair : ExecutedSegmentPair d index lower upper)
  {column : Column}
  (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
  (hRead : column[index]? = some lower)

include hRun hRead

theorem ExecutedSegmentPair.contour_effective_source {position : Nat}
    (hLower : pair.path[position]? = some pair.originalLower)
    (hUpper : pair.path[position + 1]? = some pair.originalUpper) :
    Nonempty (EffectiveAdjacentSource d column index lower) := by
  obtain ⟨execution, hRow, _⟩ := pair.contour_inside_source hLower hUpper
  exact ⟨{
    sourceIndex := pair.marker.index + position + 1,
    sourceLower := execution.lower, sourceUpper := execution.upper,
    read := {
      source_at := execution.lower_at, copy_run := hRun,
      marker := pair.marker, marker_mem := pair.member,
      marker_before := by omega,
      no_between := fun middle hLo hHi => execution.no_markers middle hLo (by omega),
      source_lower := execution.root_lower, outputIndex := index, outputCell := lower,
      output_at := hRead, output_row := hRow },
    upper_at := by simpa only [Nat.add_assoc] using execution.upper_at,
    output_index := rfl, output_cell := rfl }⟩

omit hRun hRead in
private theorem marker_parent_strict (marker : Ref) (hm : marker ∈ d.bucket) :
    FillRowsStrict (d.marker_data marker hm).parentNodes := by
  obtain ⟨hc, he⟩ := Array.getElem?_eq_some_iff.mp (d.marker_data marker hm).parent_nodes
  exact fillRowsStrict_of_columnValid (he ▸ d.ambient_valid _ hc)

theorem ExecutedSegmentPair.marker_contour_effective_source
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[i]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hLowerEq : pair.originalLower = pair.copied) (hEmpty : pair.fill = []) :
    Nonempty (EffectiveAdjacentSource d column index lower) := by
  let md := d.marker_data pair.marker pair.member
  have hRow : lower.row = md.current.row :=
    (pair.lower_shape.1.symm.trans (congrArg Cell.row hLowerEq)).trans (copyEdge_return_row pair.copy_run)
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hParentLow pair.marker pair.member
  have hTargetEq : md.targetCell.row = md.current.row := by
    apply le_antisymm _ md.target_lower
    apply le_of_not_gt
    intro hRaised
    have hFirst := fillCellsAscending_head (marker_parent_strict pair.marker pair.member) hLow md.target_at
      (by rw [hLowRow]; exact hRaised) (column := md.sourceParent.column + shift)
    rw [hLowRow] at hFirst
    change pair.fill.head? = some _ at hFirst
    simp only [hEmpty, List.head?_nil, reduceCtorEq] at hFirst
  exact d.marker_effective_adjacent_source hRun hRead pair.member (hRow.trans hTargetEq.symm)

theorem ExecutedSegmentPair.fill_contour_effective_source
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[i]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hLast : pair.fill.getLast? = some pair.originalLower) :
    Nonempty (EffectiveAdjacentSource d column index lower) := by
  let md := d.marker_data pair.marker pair.member
  have hMem : pair.originalLower ∈ fillCells md.parentNodes (md.sourceParent.column + shift)
      md.current.row md.targetCell.row :=
    (fillCellsAscending_perm _ _ _ _).mem_iff.mp (List.mem_of_getLast? hLast)
  have hRaised := (fillCells_row_bounds (marker_parent_strict pair.marker pair.member)
    md.target_at le_rfl hMem).1
  have hRaiseTarget : md.current.row < md.targetCell.row := hRaised.trans_le
    (fillCells_row_bounds (marker_parent_strict pair.marker pair.member) md.target_at le_rfl hMem).2
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hParentLow pair.marker pair.member
  obtain ⟨parentIndex, parent, before, _, _, hFill⟩ := fillCellsAscending_last
    (marker_parent_strict pair.marker pair.member) (hParentPower pair.marker pair.member)
    hLow md.target_at (by rw [hLowRow]; exact hRaiseTarget)
    (column := md.sourceParent.column + shift)
  rw [hLowRow] at hFill
  change pair.fill = _ at hFill
  rw [hFill, List.getLast?_append, List.getLast?_singleton, Option.some_or] at hLast
  have hRow : lower.row = md.targetCell.row :=
    by
      have hr := congrArg Cell.row (Option.some.inj hLast).symm
      exact pair.lower_shape.1.symm.trans hr
  exact d.marker_effective_adjacent_source hRun hRead pair.member hRow

end Pair

section Seam
variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
  {index : Nat} {lower upper : Cell}
  (seam : ExecutedSegmentSeam d index lower upper)

include seam

theorem ExecutedSegmentSeam.effective_source
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[i]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    (hRead : column[index]? = some lower) :
    Nonempty (EffectiveAdjacentSource d column index lower) := by
  obtain ⟨sourceLower, hLow, hUp, hRow, _⟩ := seam.source_predecessor hParentPower hParentLow hNoPremature
  let md := d.marker_data seam.lowMarker seam.low_member
  have hBefore : seam.lowMarker.index ≤ seam.highMarker.index - 1 := by have := seam.marker_order; omega
  have hSourceLower : md.current.row ≤ sourceLower.row := by
    rcases eq_or_lt_of_le hBefore with he | hi
    · have hSame : md.current = sourceLower := Option.some.inj (md.current_at.symm.trans (he ▸ hLow))
      exact (congrArg Cell.row hSame).le
    · exact (fillRowsStrict_of_columnValid d.source_valid _ _ _ _ md.current_at hLow hi).le
  exact ⟨{
    sourceIndex := seam.highMarker.index - 1, sourceLower := sourceLower,
    sourceUpper := (d.marker_data seam.highMarker seam.high_member).current,
    read := {
      source_at := hLow, copy_run := hRun,
      marker := seam.lowMarker, marker_mem := seam.low_member, marker_before := hBefore,
      no_between := by
        intro middle hLo hHi hMem
        obtain ⟨marker, hm, hIndex⟩ := List.mem_map.mp hMem
        apply seam.no_between marker hm
        have := seam.marker_order
        constructor <;> omega,
      source_lower := hSourceLower, outputIndex := index, outputCell := lower,
      output_at := hRead, output_row := hRow },
    upper_at := hUp, output_index := rfl, output_cell := rfl }⟩

end Seam
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedSegmentPair.contour_effective_source
#print axioms OmegaY.Expansion.ExecutedSegmentPair.marker_contour_effective_source
#print axioms OmegaY.Expansion.ExecutedSegmentPair.fill_contour_effective_source
#print axioms OmegaY.Expansion.ExecutedSegmentSeam.effective_source
