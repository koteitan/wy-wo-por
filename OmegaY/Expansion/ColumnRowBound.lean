/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ColumnRowBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ColumnCopyData
import OmegaY.Expansion.ContourPowerSteps
import OmegaY.Expansion.FinishSupport
import OmegaY.Expansion.BoundaryReferences

/-!
# A fixed upper bound for every row of a copied column

Markers keep their source rows. Filling stays below the selected target.
For contours, a source row below its marker's power cap is lifted to another
row below that cap; a source row at or above the cap is unchanged. Thus a
common bound for source rows and reference caps bounds all actual output
rows, despite possibly large changes in numerical values.
-/

namespace OmegaY.Expansion

open Canonical

def ColumnRowsBound (column : Column) (height : Row) : Prop :=
  ∀ (index : Nat) (cell : Cell), column[index]? = some cell → cell.row ≤ height

theorem ColumnRowsBound.of_mem {column : Column} {height : Row}
    (hBound : ColumnRowsBound column height) {cell : Cell} (hMem : cell ∈ column.toList) :
    cell.row ≤ height := by
  obtain ⟨index, hIndex⟩ := List.mem_iff_getElem?.mp hMem
  exact hBound index cell (by simpa only [Array.getElem?_toList] using hIndex)

theorem lift_row_le_of_cap {root target source height : Row} {scale : Nat}
    (hTargetLower : root ≤ target) (hTargetUpper : target < Row.bump root scale)
    (hSourceLower : root ≤ source) (hSourceUpper : source ≤ height)
    (hCap : Row.bump root scale ≤ height) : Row.lift root target source ≤ height := by
  by_cases hBelow : source < Row.bump root scale
  · exact (Row.lift_mem_interval hTargetLower hTargetUpper hSourceLower hBelow).2.le.trans hCap
  · rw [Row.lift_eq_of_ge_cap hTargetLower hTargetUpper (le_of_not_gt hBelow)]
    exact hSourceUpper

/-- Finishing reorders nodes and changes their values, but preserves the
input row of the same concrete node and therefore every common row bound. -/
theorem finish_rows_bound {mountain : Mountain} {cells : List Cell} {column : Column}
    (hRun : finish mountain cells = .ok column) {height : Row}
    (hBound : ∀ cell ∈ cells, cell.row ≤ height) : ColumnRowsBound column height := by
  intro index cell hCell
  obtain ⟨original, hOriginal, hSame⟩ := (finish_success_spec hRun).1.getElem hCell
  have hMem : original ∈ cells :=
    (finishSort_perm cells).mem_iff.mp (List.mem_of_getElem? hOriginal)
  rw [← hSame.1]
  exact hBound original hMem

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- The bound covers every member of the actual marker/contour/fill
decomposition, without assuming a shape property of a copied column. -/
theorem segment_rows_bound {height : Row} (hSourceBound : ColumnRowsBound d.sources height)
    {marker : Ref} (hm : marker ∈ d.bucket) {scale : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row scale)
    (hCap : Row.bump (d.marker_data marker hm).current.row scale ≤ height) :
    ∀ cell ∈ d.segment marker, cell.row ≤ height := by
  let s := d.marker_data marker hm
  obtain ⟨copied, path, gap, hResult, _, hCopiedRow, _, hContour, _, _, _, hGap⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
      d.source_top references (d.bucket.map Ref.index) s.current_at s.upper_at s.upper_left
      s.parent_nodes s.target_at s.reference s.target_lower (d.segment_run hm)
  have hLiftRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column
    d.source_nonzero d.destination.le d.source_top d.source_power (d.bucket.map Ref.index)
    s.targetCell.row s.current_at rfl hContour
  have hSourceTrace := contour_source_trace d.source_power (d.bucket.map Ref.index) s.current_at rfl
  intro cell hCell
  rw [hResult] at hCell
  rcases List.mem_append.mp hCell with hEarlier | hGapMem
  · rcases List.mem_append.mp hEarlier with hMarkerMem | hPathMem
    · have he : cell = copied := List.mem_singleton.mp hMarkerMem
      rw [he, hCopiedRow]
      exact hSourceBound marker.index s.current s.current_at
    · have hGenerated : cell.row ∈ path.map Cell.row := List.mem_map.mpr ⟨cell, hPathMem, rfl⟩
      rw [hLiftRows] at hGenerated
      obtain ⟨source, hSource, hLiftEq⟩ := List.mem_map.mp hGenerated
      have hTraceMem : source.row ∈ bumpTrace s.current.row
          (contourExponents (d.bucket.map Ref.index) marker.index s.current
            (d.sources.toList.drop (marker.index + 1))) := by
        rw [hSourceTrace]
        exact List.mem_map.mpr ⟨source, hSource, rfl⟩
      have hSourceLower : s.current.row ≤ source.row :=
        ((List.pairwise_cons.mp (bumpTrace_strict s.current.row _)).1 source.row hTraceMem).le
      have hStored : source ∈ d.sources.toList := by
        rw [contourSourceCells_eq_take] at hSource
        exact List.mem_of_mem_drop (List.mem_of_mem_take hSource)
      have hBound := lift_row_le_of_cap s.target_lower hTarget hSourceLower
        (hSourceBound.of_mem hStored) hCap
      simpa only [hLiftEq] using hBound
  · exact (hGap cell hGapMem).2.trans (hTarget.le.trans hCap)

theorem candidates_rows_bound {height : Row} (hSourceBound : ColumnRowsBound d.sources height)
    (hCaps : ∀ marker (hm : marker ∈ d.bucket), ∃ scale,
      (d.marker_data marker hm).targetCell.row < Row.bump (d.marker_data marker hm).current.row scale ∧
        Row.bump (d.marker_data marker hm).current.row scale ≤ height) :
    ∀ cell ∈ d.candidates, cell.row ≤ height := by
  intro cell hCell
  obtain ⟨marker, hm, hCell⟩ := List.mem_flatMap.mp hCell
  obtain ⟨scale, hTarget, hCap⟩ := hCaps marker hm
  exact d.segment_rows_bound hSourceBound hm hTarget hCap cell hCell

/-- Every node in the actual returned array obeys the same height bound.
No assumption of copied-column normality, power steps, or stopping is used. -/
theorem copyColumn_rows_bound {height : Row} (hSourceBound : ColumnRowsBound d.sources height)
    (hCaps : ∀ marker (hm : marker ∈ d.bucket), ∃ scale,
      (d.marker_data marker hm).targetCell.row < Row.bump (d.marker_data marker hm).current.row scale ∧
        Row.bump (d.marker_data marker hm).current.row scale ≤ height)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column) :
    ColumnRowsBound column height :=
  finish_rows_bound (d.copyColumn_eq_finish.symm.trans hRun)
    (d.candidates_rows_bound hSourceBound hCaps)

end ColumnCopyData

/-- Fresh dynamic boundary references all lie within the original root
caps, whose upper bounds are at most the original last-top row. -/
theorem ColumnCopyData.copyColumn_rows_bound_of_boundary {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {references : List Ref}
    {sourceColumn shift rootColumn boundaryColumn : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift rootColumn)
    (hLast : 1 < last) (hBaseSource : p.reduced[sourceColumn]? = some d.sources)
    (hBoundaryRows : RootRowsInColumn p mountain boundaryColumn)
    (hMap : p.boundaries.mapM (below mountain boundaryColumn) = .ok references)
    {height : Row} (hSourceBound : ColumnRowsBound d.sources height)
    (hLastTop : p.lastTop.row ≤ height) {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift rootColumn = .ok column) :
    ColumnRowsBound column height := by
  apply d.copyColumn_rows_bound hSourceBound ?_ hRun
  intro marker hm
  let s := d.marker_data marker hm
  have hBaseRead : Canonical.cellAt p.reduced marker = .ok s.current :=
    cellAt_ok_iff.mpr ⟨d.sources,
      by simpa only [d.marker_columns marker hm] using hBaseSource, s.current_at⟩
  obtain ⟨target, ceiling, scale, hReference, _, hHigh, hPower, hCap⟩ :=
    hBoundaryRows.marker_interval d.ambient_valid hLast hMap hm hBaseRead
  have hTargetEq : target = s.targetCell.row := Except.ok.inj (hReference.symm.trans s.reference)
  exact ⟨scale, by simpa only [hTargetEq, hPower] using hHigh,
    by simpa only [hPower] using hCap.trans hLastTop⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.segment_rows_bound
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_rows_bound
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_rows_bound_of_boundary
