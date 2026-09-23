/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCellFatherBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ContourFatherBound

/-!
# Every cell actually copied obeys the raw father-upper bound

Candidates are classified by their real marker, contour, or fill execution.
Finishing preserves row and left reference together at the actual index.
No raw parent-search conclusion or copied normality is used.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem DynamicBlockState.segment_father_bound
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    (hSource : p.reduced[next]? = some d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket)
    {cell : Cell} (hCell : cell ∈ d.segment marker) : CellRawFatherBound ambient cell := by
  let md := d.marker_data marker hm
  obtain ⟨copied, path, gap, hResult, hCopy, _, _, hContour, hFill, _, _, _⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero
      d.destination.le d.source_top references (d.bucket.map Ref.index)
      md.current_at md.upper_at md.upper_left md.parent_nodes md.target_at md.reference
      md.target_lower (d.segment_run hm)
  rw [hResult] at hCell
  rcases List.mem_append.mp hCell with hFirst | hGap
  · rcases List.mem_append.mp hFirst with hMarker | hPath
    · have he : cell = copied := List.mem_singleton.mp hMarker
      subst cell
      have hRead : Canonical.cellAt p.reduced ⟨next, marker.index⟩ = .ok md.current :=
        cellAt_ok_iff.mpr ⟨d.sources, hSource, md.current_at⟩
      exact s.copyEdge_source_row_father_bound hRead hCopy
    · obtain ⟨position, hRead⟩ := List.mem_iff_getElem?.mp hPath
      obtain ⟨execution⟩ := contour_execution_at d.source_power (d.bucket.map Ref.index)
        md.current_at le_rfl rfl
        (by simpa only [Row.lift_at_root] using hContour) hRead
      exact s.contourNth_father_bound hLast d hSource hm execution
  · obtain ⟨hp, hNodes⟩ := Array.getElem?_eq_some_iff.mp md.parent_nodes
    have hValid : ColumnValid ambient (md.sourceParent.column +
        block * (p.reduced.size - 1 - p.root.column)) md.parentNodes :=
      hNodes ▸ d.ambient_valid _ hp
    have hStrict := fillRowsStrict_of_columnValid hValid
    have hUpperRead : lookup ambient ⟨next, marker.index + 1⟩ = .ok md.upper :=
      lookup_ok_iff.mpr ⟨d.sources, d.source_column, md.upper_at⟩
    have hParentLeft := (d.source_valid.stored_valid _ _ _ md.upper_at md.upper_left).1
    have hExpected := fill_eq_cells hUpperRead md.upper_left md.parent_nodes hStrict
      md.target_at le_rfl (Nat.add_lt_add_right hParentLeft _) (low := md.current.row)
    have hGapEq : gap = fillCells md.parentNodes
        (md.sourceParent.column + block * (p.reduced.size - 1 - p.root.column))
        md.current.row md.targetCell.row := Except.ok.inj (hFill.symm.trans hExpected)
    exact fillCells_rawFatherBound md.parent_nodes hStrict md.target_at le_rfl (hGapEq ▸ hGap)

theorem DynamicBlockState.candidates_father_bound
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    (hSource : p.reduced[next]? = some d.sources) :
    ∀ cell ∈ d.candidates, CellRawFatherBound ambient cell := by
  intro cell hCell
  obtain ⟨marker, hm, hMem⟩ := List.mem_flatMap.mp hCell
  exact s.segment_father_bound hLast d hSource hm hMem

/-- The complete actual finished array has raw D at every cell. The real
copy state supplies the source data; the output bound is not a premise. -/
theorem DynamicBlockState.actual_copyColumn_father_bound
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hNext : next < p.reduced.size) {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∀ (index : Nat) (cell : Cell), column[index]? = some cell → CellRawFatherBound ambient cell := by
  obtain ⟨d, _, _, _⟩ := s.column_data hLast hNext
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  obtain ⟨actual, hFinish, hShape, _⟩ := d.finish_input.finish
  have he : actual = column := Except.ok.inj
    (hFinish.symm.trans (d.copyColumn_eq_finish.symm.trans hRun))
  subst actual
  intro index cell hRead
  obtain ⟨original, hOriginal, hSameShape⟩ := hShape.getElem hRead
  have hMem : original ∈ d.candidates :=
    (finishSort_perm d.candidates).mem_iff.mp (List.mem_of_getElem? hOriginal)
  exact (s.candidates_father_bound hLast d hSource original hMem).sameShape hSameShape

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.segment_father_bound
#print axioms OmegaY.Expansion.DynamicBlockState.candidates_father_bound
#print axioms OmegaY.Expansion.DynamicBlockState.actual_copyColumn_father_bound
