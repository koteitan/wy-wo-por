/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/HighRowPreservation.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ColumnRootRows
import OmegaY.Expansion.ColumnRowBound

/-!
# Exact high-row support of an actual copied column

Every marker target lies below its own power cap, and all these caps are
at or below one common threshold. Markers and fill cells stay strictly
below the threshold. Contour rows reaching it are already fixed by their
lift. The result concerns rows only, not numerical values or stored legs.
-/

namespace OmegaY.Expansion

open Canonical

/-- A lifted source that reaches the common threshold was already above
its marker's cap, so its row is unchanged. -/
theorem lift_eq_source_of_high {root target source threshold : Row} {scale : Nat}
    (hTargetLower : root ≤ target) (hTarget : target < Row.bump root scale)
    (hSourceLower : root ≤ source) (hCap : Row.bump root scale ≤ threshold)
    (hHigh : threshold ≤ Row.lift root target source) :
    Row.lift root target source = source := by
  by_cases hBelow : source < Row.bump root scale
  · have hLiftBelow := (Row.lift_mem_interval hTargetLower hTarget hSourceLower hBelow).2
    exact False.elim ((not_lt_of_ge (hCap.trans hHigh)) hLiftBelow)
  · exact Row.lift_eq_of_ge_cap hTargetLower hTarget (le_of_not_gt hBelow)

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- A high cell of an actual segment comes from an actual source contour
cell with the same row. Neither the marker nor the fill can produce it. -/
theorem segment_high_row_source {threshold : Row} {marker : Ref} (hm : marker ∈ d.bucket)
    {scale : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row scale)
    (hCap : Row.bump (d.marker_data marker hm).current.row scale ≤ threshold)
    {cell : Cell} (hCell : cell ∈ d.segment marker) (hHigh : threshold ≤ cell.row) :
    cell.row ∈ d.sources.toList.map Cell.row := by
  let s := d.marker_data marker hm
  obtain ⟨copied, path, gap, hResult, _, hCopiedRow, _, hContour, _, _, _, hGap⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
      d.source_top references (d.bucket.map Ref.index) s.current_at s.upper_at s.upper_left
      s.parent_nodes s.target_at s.reference s.target_lower (d.segment_run hm)
  have hTargetBelow : s.targetCell.row < threshold := hTarget.trans_le hCap
  rw [hResult] at hCell
  rcases List.mem_append.mp hCell with hBefore | hGapMem
  · rcases List.mem_append.mp hBefore with hMarkerMem | hPathMem
    · have he : cell = copied := List.mem_singleton.mp hMarkerMem
      have hLow : cell.row < threshold := by
        rw [he, hCopiedRow]
        exact s.target_lower.trans_lt hTargetBelow
      exact False.elim ((not_lt_of_ge hHigh) hLow)
    · have hLiftRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column
        d.source_nonzero d.destination.le d.source_top d.source_power (d.bucket.map Ref.index)
        s.targetCell.row s.current_at rfl hContour
      have hGenerated : cell.row ∈ path.map Cell.row := List.mem_map.mpr ⟨cell, hPathMem, rfl⟩
      rw [hLiftRows] at hGenerated
      obtain ⟨source, hSource, hLiftEq⟩ := List.mem_map.mp hGenerated
      have hSourceTrace := contour_source_trace d.source_power (d.bucket.map Ref.index) s.current_at rfl
      have hTraceMem : source.row ∈ bumpTrace s.current.row
          (contourExponents (d.bucket.map Ref.index) marker.index s.current
            (d.sources.toList.drop (marker.index + 1))) := by
        rw [hSourceTrace]
        exact List.mem_map.mpr ⟨source, hSource, rfl⟩
      have hSourceLower : s.current.row ≤ source.row :=
        ((List.pairwise_cons.mp (bumpTrace_strict s.current.row _)).1 source.row hTraceMem).le
      have hFixed : Row.lift s.current.row s.targetCell.row source.row = source.row :=
        lift_eq_source_of_high s.target_lower hTarget hSourceLower hCap
          (by simpa only [hLiftEq] using hHigh)
      have hStored : source ∈ d.sources.toList := by
        rw [contourSourceCells_eq_take] at hSource
        exact List.mem_of_mem_drop (List.mem_of_mem_take hSource)
      exact List.mem_map.mpr ⟨source, hStored, hFixed.symm.trans hLiftEq⟩
  · exact False.elim ((not_lt_of_ge hHigh) ((hGap cell hGapMem).2.trans_lt hTargetBelow))

section CommonThreshold

variable {threshold : Row}
  (hCaps : ∀ marker (hm : marker ∈ d.bucket), ∃ scale,
    (d.marker_data marker hm).targetCell.row < Row.bump (d.marker_data marker hm).current.row scale ∧
      Row.bump (d.marker_data marker hm).current.row scale ≤ threshold)

include hCaps

/-- The full actual candidate list introduces no row at or above the
common threshold that was absent from the source column. -/
theorem candidates_high_row_source {row : Row} (hHigh : threshold ≤ row)
    (hRow : row ∈ d.candidates.map Cell.row) : row ∈ d.sources.toList.map Cell.row := by
  obtain ⟨cell, hCell, hCellRow⟩ := List.mem_map.mp hRow
  obtain ⟨marker, hm, hSegment⟩ := List.mem_flatMap.mp hCell
  obtain ⟨scale, hTarget, hCap⟩ := hCaps marker hm
  simpa only [hCellRow] using d.segment_high_row_source hm hTarget hCap hSegment
    (by simpa only [hCellRow] using hHigh)

/-- Exact equality of high-row membership in the source and the actual
returned array. Parent power/low-support assumptions are unnecessary for
this row-only theorem; segment success follows from the input record. -/
theorem copyColumn_high_rows_iff (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {row : Row} (hHigh : threshold ≤ row) :
    row ∈ column.toList.map Cell.row ↔ row ∈ d.sources.toList.map Cell.row := by
  rw [finish_rows_mem_iff (d.copyColumn_eq_finish.symm.trans hRun)]
  constructor
  · exact d.candidates_high_row_source hCaps hHigh
  · intro hRow
    obtain ⟨source, hSource, hSourceRow⟩ := List.mem_map.mp hRow
    obtain ⟨sourceIndex, hRead⟩ := List.mem_iff_getElem?.mp hSource
    have hSourceRead : d.sources[sourceIndex]? = some source := by
      simpa only [Array.getElem?_toList] using hRead
    have hRowMem := d.source_row_mem_candidates_of_caps hNoPremature hSourceRead (by
      intro marker hm _
      obtain ⟨scale, hTarget, hCap⟩ := hCaps marker hm
      exact ⟨scale, hTarget, hCap.trans (by simpa only [hSourceRow] using hHigh)⟩)
    simpa only [hSourceRow] using hRowMem

/-- A high actual output read has an actual source-array witness with the
same row. Its original value, index, and stored left leg are not identified. -/
theorem copyColumn_high_read_to_source {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {index : Nat} {cell : Cell} (hRead : column[index]? = some cell)
    (hHigh : threshold ≤ cell.row) :
    ∃ (sourceIndex : Nat) (sourceCell : Cell),
      d.sources[sourceIndex]? = some sourceCell ∧ sourceCell.row = cell.row := by
  have hRow : cell.row ∈ column.toList.map Cell.row := List.mem_map.mpr
    ⟨cell, List.mem_of_getElem? (by simpa only [Array.getElem?_toList] using hRead), rfl⟩
  have hCandidates := (finish_rows_mem_iff (d.copyColumn_eq_finish.symm.trans hRun) cell.row).mp hRow
  obtain ⟨sourceCell, hSource, hSourceRow⟩ := List.mem_map.mp (d.candidates_high_row_source hCaps hHigh hCandidates)
  obtain ⟨sourceIndex, hSourceRead⟩ := List.mem_iff_getElem?.mp hSource
  exact ⟨sourceIndex, sourceCell, by simpa only [Array.getElem?_toList] using hSourceRead, hSourceRow⟩

/-- Every high source read survives at a fresh actual output-array index. -/
theorem copyColumn_high_read_from_source (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {sourceIndex : Nat} {sourceCell : Cell} (hSource : d.sources[sourceIndex]? = some sourceCell)
    (hHigh : threshold ≤ sourceCell.row) :
    ∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ cell.row = sourceCell.row := by
  apply d.copyColumn_source_row_read_of_caps hNoPremature hRun hSource
  intro marker hm _
  obtain ⟨scale, hTarget, hCap⟩ := hCaps marker hm
  exact ⟨scale, hTarget, hCap.trans hHigh⟩

/-- If the original strict-below selector chooses a high row, the copied
selector chooses precisely the same row. The new index and numerical cell
are allowed to differ. A ceiling merely above the threshold would not be
sufficient: the selected row itself must be high. -/
theorem copyColumn_below_high_source (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {ceiling : Row} {sourceRef : Ref} {sourceCell : Cell}
    (hSourceBelow : below mountain sourceColumn ceiling = .ok sourceRef)
    (hSourceRead : d.sources[sourceRef.index]? = some sourceCell)
    (hHigh : threshold ≤ sourceCell.row) :
    ∃ (ref : Ref) (cell : Cell),
      below (mountain.push column) mountain.size ceiling = .ok ref ∧
      Canonical.cellAt (mountain.push column) ref = .ok cell ∧
      ref.column = mountain.size ∧ cell.row = sourceCell.row := by
  obtain ⟨_, selected, hSelected, hSelectedBelow⟩ := below_result d.source_column hSourceBelow
  have hSelectedEq : selected = sourceCell := Option.some.inj (hSelected.symm.trans hSourceRead)
  have hSourceBound : sourceCell.row < ceiling := by simpa only [hSelectedEq] using hSelectedBelow
  obtain ⟨floorIndex, floorCell, hFloor, hFloorRow⟩ :=
    d.copyColumn_high_read_from_source hCaps hNoPremature hRun hSourceRead hHigh
  have hFloorRead : Canonical.cellAt (mountain.push column) ⟨mountain.size, floorIndex⟩ = .ok floorCell :=
    cellAt_ok_iff.mpr ⟨column, by simp, hFloor⟩
  obtain ⟨actualColumn, hActualRun, _, _, _, hMountain⟩ := d.copyColumn_valid
  have hColumnEq : actualColumn = column := Except.ok.inj (hActualRun.symm.trans hRun)
  subst actualColumn
  obtain ⟨ref, cell, hBelow, hRead, hColumn, hAbove, hBound⟩ :=
    below_between hMountain hFloorRead (by simpa only [hFloorRow] using hSourceBound)
  have hSourceLe : sourceCell.row ≤ cell.row := by simpa only [hFloorRow] using hAbove
  obtain ⟨nodes, hNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  have hNodesEq : nodes = column := Option.some.inj (hNodes.symm.trans (by simp [hColumn]))
  subst nodes
  obtain ⟨oldIndex, oldCell, hOldRead, hOldRow⟩ :=
    d.copyColumn_high_read_to_source hCaps hRun hCell (hHigh.trans hSourceLe)
  have hStrict : StrictMono (fun i : Fin d.sources.size => d.sources[i.val].row) := by
    intro i j hij
    exact d.source_valid.rows_strict _ _ _ _ (Array.getElem?_eq_getElem i.isLt)
      (Array.getElem?_eq_getElem j.isLt) hij
  have hSelectedMax : oldCell.row ≤ sourceCell.row :=
    below_max_row d.source_column hStrict hSourceBelow hSourceRead hOldRead
      (by simpa only [hOldRow] using hBound)
  have hCellLe : cell.row ≤ sourceCell.row := by simpa only [hOldRow] using hSelectedMax
  exact ⟨ref, cell, hBelow, hRead, hColumn, le_antisymm hCellLe hSourceLe⟩

/-- Appending later copied columns preserves the same exact high-row
selection in the completed parent column. -/
theorem copyColumn_below_high_source_preserved (hNoPremature : NoPrematureOne d.sources)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {later : Mountain} (hPreserve : PreservesColumns (mountain.push column) later)
    {ceiling : Row} {sourceRef : Ref} {sourceCell : Cell}
    (hSourceBelow : below mountain sourceColumn ceiling = .ok sourceRef)
    (hSourceRead : d.sources[sourceRef.index]? = some sourceCell)
    (hHigh : threshold ≤ sourceCell.row) :
    ∃ (ref : Ref) (cell : Cell), below later mountain.size ceiling = .ok ref ∧
      Canonical.cellAt later ref = .ok cell ∧
      ref.column = mountain.size ∧ cell.row = sourceCell.row := by
  obtain ⟨ref, cell, hBelow, hRead, hColumn, hRow⟩ :=
    d.copyColumn_below_high_source hCaps hNoPremature hRun hSourceBelow hSourceRead hHigh
  obtain ⟨nodes, hNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  exact ⟨ref, cell, (hPreserve.below (by simp) ceiling).trans hBelow,
    cellAt_ok_iff.mpr ⟨nodes, hPreserve.column_read hNodes, hCell⟩, hColumn, hRow⟩

end CommonThreshold

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.lift_eq_source_of_high
#print axioms OmegaY.Expansion.ColumnCopyData.segment_high_row_source
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_high_rows_iff
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_high_read_to_source
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_high_read_from_source
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_high_source
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_high_source_preserved
