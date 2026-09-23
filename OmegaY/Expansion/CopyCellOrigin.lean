/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CopyCellOrigin.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveCopy
import OmegaY.Expansion.ContourExecutionAt

/-!
# Origin of a single actual copied cell

The real finish shape, segment execution, and indexed contour execution
give a complete cell classification. Reference endpoints are classified
by their actual fill generation here; an endpoint may also be the effective
occurrence of a marker. No copied numerical-parent recognition is used.
-/

namespace OmegaY.Expansion

open Canonical

/-- Each constructor records a true program origin. The effective case
is obtained by inverting contour execution, not by assuming a source row.
Marker and fill cells retain their actual pre-backfill row and left shape. -/
inductive CopiedCellOrigin {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (column : Column) (index : Nat) (cell : Cell) : Type
  | effective (sourceIndex : Nat) (sourceCell : Cell)
      (read : EffectiveCopyRead d sourceIndex sourceCell column)
      (output_index : read.outputIndex = index) (output_cell : read.outputCell = cell)
      (unmarked : sourceIndex ∉ d.bucket.map Ref.index)
  | physicalMarker (marker : Ref) (hm : marker ∈ d.bucket) (copied : Cell)
      (copy_run : copyEdge mountain ⟨sourceColumn, marker.index⟩ shift rootColumn
        (d.marker_data marker hm).current.row = .ok copied)
      (copied_row : copied.row = (d.marker_data marker hm).current.row)
      (shape : SameShape copied cell)
  | referenceGap (marker : Ref) (hm : marker ∈ d.bucket) (gap : List Cell) (original : Cell)
      (fill_run : fill mountain ⟨sourceColumn, marker.index + 1⟩ shift
        (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row = .ok gap)
      (member : original ∈ gap) (shape : SameShape original cell)
      (above_marker : (d.marker_data marker hm).current.row < cell.row)
      (below_target : cell.row ≤ (d.marker_data marker hm).targetCell.row)

/-- Every cell read from the actual returned column has one of the three
program origins. No successful segment, source origin, or finish shape is
supplied by the caller. -/
theorem ColumnCopyData.copyColumn_cell_origin
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {index : Nat} {cell : Cell} (hRead : column[index]? = some cell) :
    Nonempty (CopiedCellOrigin d column index cell) := by
  obtain ⟨actual, hFinish, hShape, _⟩ := d.finish_input.finish
  have he : actual = column := Except.ok.inj
    (hFinish.symm.trans (d.copyColumn_eq_finish.symm.trans hRun))
  subst actual
  obtain ⟨original, hOriginal, hSameShape⟩ := hShape.getElem hRead
  have hCandidate : original ∈ d.candidates :=
    (finishSort_perm d.candidates).mem_iff.mp (List.mem_of_getElem? hOriginal)
  obtain ⟨marker, hm, hSegment⟩ := List.mem_flatMap.mp hCandidate
  let md := d.marker_data marker hm
  obtain ⟨copied, path, gap, hResult, hCopy, hCopyRow, _, hContour, hFill, _, _, hGap⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
      d.source_top references (d.bucket.map Ref.index) md.current_at md.upper_at md.upper_left
      md.parent_nodes md.target_at md.reference md.target_lower (d.segment_run hm)
  rw [hResult] at hSegment
  rcases List.mem_append.mp hSegment with hBefore | hGapMember
  · rcases List.mem_append.mp hBefore with hMarker | hPathMember
    · have hEqual : original = copied := List.mem_singleton.mp hMarker
      subst original
      exact ⟨.physicalMarker marker hm copied hCopy hCopyRow hSameShape⟩
    · obtain ⟨position, hPathRead⟩ := List.mem_iff_getElem?.mp hPathMember
      have hContourLift : contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn
          marker.index (Row.lift md.current.row md.targetCell.row md.current.row) md.current
          (d.sources.toList.drop (marker.index + 1)) = .ok path := by
        simpa only [Row.lift_at_root] using hContour
      obtain ⟨execution⟩ := contour_execution_at d.source_power (d.bucket.map Ref.index)
        md.current_at le_rfl rfl hContourLift hPathRead
      let sourceIndex := marker.index + position + 1
      let read : EffectiveCopyRead d sourceIndex execution.upper column := {
        source_at := execution.upper_at
        copy_run := hRun
        marker := marker
        marker_mem := hm
        marker_before := by dsimp [sourceIndex]; omega
        no_between := execution.no_markers
        source_lower := execution.root_lower.trans execution.source_rows.le
        outputIndex := index
        outputCell := cell
        output_at := hRead
        output_row := hSameShape.1.symm.trans execution.copied_row }
      exact ⟨.effective sourceIndex execution.upper read rfl rfl
        (execution.no_markers sourceIndex (by dsimp [sourceIndex]; omega) le_rfl)⟩
  · exact ⟨.referenceGap marker hm gap original hFill hGapMember hSameShape
      (by simpa only [hSameShape.1] using (hGap original hGapMember).1)
      (by simpa only [hSameShape.1] using (hGap original hGapMember).2)⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_cell_origin
