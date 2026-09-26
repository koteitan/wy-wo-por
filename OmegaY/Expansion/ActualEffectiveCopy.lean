/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveCopy.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ColumnRootRows
import OmegaY.Expansion.ColumnPower
import OmegaY.Expansion.DynamicBlockStep

/-!
# Actual effective occurrences of all source nodes

The controlling marker is the greatest actual marker at or before the source
index. A marker's effective occurrence is its target row, while a nonmarker's
occurrence is the actual lifted contour row. Sorting and backfill supply a
fresh output index. The output occurrence is constructed, never assumed.
-/

namespace OmegaY.Expansion

open Canonical

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- The full lifted row of a real source-contour member occurs among the
executed segment candidates; no stationary-row or source-cap premise is used. -/
theorem segment_lifted_source_row_mem {marker : Ref} (hm : marker ∈ d.bucket)
    {sourceCell : Cell}
    (hSource : sourceCell ∈ contourSourceCells (d.bucket.map Ref.index) marker.index
      (d.marker_data marker hm).current (d.sources.toList.drop (marker.index + 1))) :
    Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row
      sourceCell.row ∈ (d.segment marker).map Cell.row := by
  let md := d.marker_data marker hm
  obtain ⟨copied, path, gap, hResult, _, _, _, hContour, _, _, _, _⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
      d.source_top references (d.bucket.map Ref.index) md.current_at md.upper_at md.upper_left
      md.parent_nodes md.target_at md.reference md.target_lower (d.segment_run hm)
  have hRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column
    d.source_nonzero d.destination.le d.source_top d.source_power (d.bucket.map Ref.index)
    md.targetCell.row md.current_at rfl hContour
  have hPath : Row.lift md.current.row md.targetCell.row sourceCell.row ∈ path.map Cell.row := by
    rw [hRows]
    exact List.mem_map.mpr ⟨sourceCell, hSource, rfl⟩
  obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hPath
  rw [hResult]
  exact List.mem_map.mpr ⟨cell, by simp [hCell], hRow⟩

end ColumnCopyData

/-- The source read, actual controlling marker, execution, and fresh output
read are retained together. Marker endpoints use the target occurrence. -/
structure EffectiveCopyRead {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (sourceIndex : Nat) (sourceCell : Cell) (column : Column) where
  source_at : d.sources[sourceIndex]? = some sourceCell
  copy_run : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column
  marker : Ref
  marker_mem : marker ∈ d.bucket
  marker_before : marker.index ≤ sourceIndex
  no_between : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
    middle ∉ d.bucket.map Ref.index
  source_lower : (d.marker_data marker marker_mem).current.row ≤ sourceCell.row
  outputIndex : Nat
  outputCell : Cell
  output_at : column[outputIndex]? = some outputCell
  output_row : outputCell.row = Row.lift (d.marker_data marker marker_mem).current.row
    (d.marker_data marker marker_mem).targetCell.row sourceCell.row

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- Parent-column power/low support concerns already available input columns
only. Actual dynamic states below supply both automatically. -/
theorem effective_copy_read
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {sourceIndex : Nat} {sourceCell : Cell} (hSource : d.sources[sourceIndex]? = some sourceCell) :
    Nonempty (EffectiveCopyRead d sourceIndex sourceCell column) := by
  obtain ⟨marker, hm, hBefore, hNoBetween, hLower, hCases⟩ := d.source_partition hNoPremature hSource
  obtain ⟨index, cell, hRead, hRow⟩ : ∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧
      cell.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row sourceCell.row := by
    rcases hCases with ⟨_, hSame⟩ | ⟨_, hContour⟩
    · obtain ⟨index, cell, hRead, hRow⟩ :=
        (d.copyColumn_marker_target_reads hParentPower hParentLow hRun hm).2
      exact ⟨index, cell, hRead, by simpa only [hSame, Row.lift_at_root] using hRow⟩
    · exact finish_row_read (d.copyColumn_eq_finish.symm.trans hRun)
        (d.segment_row_mem_candidates hm (d.segment_lifted_source_row_mem hm hContour))
  exact ⟨{
    source_at := hSource
    copy_run := hRun
    marker := marker
    marker_mem := hm
    marker_before := hBefore
    no_between := hNoBetween
    source_lower := hLower
    outputIndex := index
    outputCell := cell
    output_at := hRead
    output_row := hRow }⟩

end ColumnCopyData

namespace EffectiveCopyRead

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
  {sourceIndex : Nat} {sourceCell : Cell} {column : Column}
  (read : EffectiveCopyRead d sourceIndex sourceCell column)

def outputRef : Ref := ⟨mountain.size, read.outputIndex⟩

theorem output_read : Canonical.cellAt (mountain.push column) read.outputRef = .ok read.outputCell :=
  cellAt_ok_iff.mpr ⟨column, by simp [outputRef], read.output_at⟩

theorem output_source_column : read.outputRef.column = sourceColumn + shift := d.destination.symm

theorem source_row_le_output : sourceCell.row ≤ read.outputCell.row := by
  rw [read.output_row]
  exact Row.lift_ge_source (d.marker_data read.marker read.marker_mem).target_lower read.source_lower

theorem output_real (hSourceReal : 0 < sourceIndex) : 0 < read.outputIndex := by
  have hSourcePositive := d.source_valid.rows_strict 0 sourceIndex phantom sourceCell
    d.source_valid.phantom read.source_at hSourceReal
  change (0 : Row) < sourceCell.row at hSourcePositive
  have hPositive := hSourcePositive.trans_le read.source_row_le_output
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans read.copy_run)
  subst actual
  by_contra hn
  have hZero : read.outputIndex = 0 := by omega
  have hPhantom : read.outputCell = phantom :=
    Option.some.inj ((hZero ▸ read.output_at).symm.trans hValid.phantom)
  rw [hPhantom] at hPositive
  exact (lt_irrefl (0 : Row)) hPositive

/-- Maximality determines the marker even though the proof chooses it from
a finite list. Hence the lifted row is independent of the chosen witness. -/
theorem marker_eq (other : EffectiveCopyRead d sourceIndex sourceCell column) :
    read.marker = other.marker := by
  have hIndex : read.marker.index = other.marker.index := by
    apply Nat.le_antisymm
    · by_contra hn
      exact other.no_between read.marker.index (by omega) read.marker_before
        (List.mem_map.mpr ⟨read.marker, read.marker_mem, rfl⟩)
    · by_contra hn
      exact read.no_between other.marker.index (by omega) other.marker_before
        (List.mem_map.mpr ⟨other.marker, other.marker_mem, rfl⟩)
  have hColumn := (d.marker_columns read.marker read.marker_mem).trans
    (d.marker_columns other.marker other.marker_mem).symm
  cases hRead : read.marker
  cases hOther : other.marker
  simp only [hRead, hOther] at hColumn hIndex
  simp only [Ref.mk.injEq]
  exact ⟨hColumn, hIndex⟩

theorem unique (other : EffectiveCopyRead d sourceIndex sourceCell column) :
    read.marker = other.marker ∧ read.outputIndex = other.outputIndex ∧
      read.outputCell = other.outputCell := by
  have hMarker := read.marker_eq other
  have hMarkerIndex := congrArg Ref.index hMarker
  have hCurrent : (d.marker_data read.marker read.marker_mem).current =
      (d.marker_data other.marker other.marker_mem).current := by
    have hIndices : d.sources[read.marker.index]? = d.sources[other.marker.index]? :=
      congrArg (fun index : Nat => d.sources[index]?) hMarkerIndex
    exact Option.some.inj
      ((d.marker_data read.marker read.marker_mem).current_at.symm.trans
        (hIndices.trans (d.marker_data other.marker other.marker_mem).current_at))
  have hCurrentRow := congrArg Cell.row hCurrent
  have hTargetRow : (d.marker_data read.marker read.marker_mem).targetCell.row =
      (d.marker_data other.marker other.marker_mem).targetCell.row := by
    have hReference := (d.marker_data read.marker read.marker_mem).reference
    rw [hCurrentRow] at hReference
    exact Except.ok.inj
      (hReference.symm.trans (d.marker_data other.marker other.marker_mem).reference)
  have hRow : read.outputCell.row = other.outputCell.row := by
    rw [read.output_row, other.output_row, hCurrentRow, hTargetRow]
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans read.copy_run)
  subst actual
  have hIndex : read.outputIndex = other.outputIndex := by
    apply Nat.le_antisymm
    · by_contra hn
      have hLt := hValid.rows_strict _ _ _ _ other.output_at read.output_at (by omega)
      exact (ne_of_lt hLt) hRow.symm
    · by_contra hn
      have hLt := hValid.rows_strict _ _ _ _ read.output_at other.output_at (by omega)
      exact (ne_of_lt hLt) hRow
  exact ⟨hMarker, hIndex, Option.some.inj (read.output_at.symm.trans (hIndex ▸ other.output_at))⟩

end EffectiveCopyRead

/-- The real state supplies the complete source data and all old-column
support. No output occurrence, copied power step, or normality is an input. -/
theorem DynamicBlockState.actual_effective_copy_read
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hNext : next < p.reduced.size) {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
    {sourceIndex : Nat} {sourceCell : Cell}
    (hSource : Canonical.cellAt p.reduced ⟨next, sourceIndex⟩ = .ok sourceCell) :
    ∃ d : ColumnCopyData ambient p.marked references next
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column,
      p.reduced[next]? = some d.sources ∧ Nonempty (EffectiveCopyRead d sourceIndex sourceCell column) := by
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast hNext
  have hSourceColumn : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp hSource
  have he : nodes = d.sources := Option.some.inj (hNodes.symm.trans hSourceColumn)
  exact ⟨d, hSourceColumn, d.effective_copy_read hParentPower hParentLow hNoPremature hRun (he ▸ hRead)⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.segment_lifted_source_row_mem
#print axioms OmegaY.Expansion.ColumnCopyData.effective_copy_read
#print axioms OmegaY.Expansion.EffectiveCopyRead.output_read
#print axioms OmegaY.Expansion.EffectiveCopyRead.output_real
#print axioms OmegaY.Expansion.EffectiveCopyRead.unique
#print axioms OmegaY.Expansion.DynamicBlockState.actual_effective_copy_read
