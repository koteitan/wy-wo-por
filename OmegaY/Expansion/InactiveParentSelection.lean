/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InactiveParentSelection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.HighRowPreservation
import OmegaY.Expansion.CopiedParentTop

/-!
# Exact copied selection above one controlling marker cap

Only the cap of the greatest source marker at or below the selected source
node is required to lie below that node. Lower marker segments cannot reach
it; later marker segments cannot enter its actual source strict-below
window. This works below the global last-top threshold as well as above it.

All selected target cells are actual output reads at freshly witnessed
indices. No copied Normal, desired below result, or global cap bound is an
assumption. The top case has no upper-row restriction on the query.
-/

namespace OmegaY.Expansion

open Canonical

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- A source node above its controlling marker's cap is in that marker's
actual contour and contributes its unchanged row to the actual candidates. -/
theorem inactive_source_row_mem_candidates (hNoPremature : NoPrematureOne d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {sourceCell : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell) (hIndex : marker.index ≤ sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
      middle ∉ d.bucket.map Ref.index) {scale : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row scale)
    (hCap : Row.bump (d.marker_data marker hm).current.row scale ≤ sourceCell.row) :
    sourceCell.row ∈ d.candidates.map Cell.row := by
  let s := d.marker_data marker hm
  have hRowLt : s.current.row < sourceCell.row := s.target_lower.trans_lt (hTarget.trans_le hCap)
  have hStrict : marker.index < sourceIndex := by
    rcases eq_or_lt_of_le hIndex with he | hl
    · have hSame : s.current = sourceCell := Option.some.inj
        (s.current_at.symm.trans (by simpa only [he] using hSource))
      have : s.current.row = sourceCell.row := congrArg Cell.row hSame
      exact False.elim ((ne_of_lt hRowLt) this)
    · exact hl
  have hContour := mem_contourSourceCells_of_no_between hNoPremature (d.bucket.map Ref.index)
    s.current_at hSource hStrict hNoBetween rfl
  have hSegment := d.segment_source_row_mem_of_cap hm hContour hTarget hCap
  obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hSegment
  exact List.mem_map.mpr ⟨cell, List.mem_flatMap.mpr ⟨marker, hm, hCell⟩, hRow⟩

/-- In the selected source window, only the controlling marker can
contribute output rows at or above the source parent. Its cap fixes those
rows, so each is an actual source row. -/
theorem candidates_inactive_window_source
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceRef : Ref} {sourceCell : Cell}
    {query : Row} (hSourceBelow : below mountain sourceColumn query = .ok sourceRef)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceRef.index →
      middle ∉ d.bucket.map Ref.index) {scale : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row scale)
    (hCap : Row.bump (d.marker_data marker hm).current.row scale ≤ sourceCell.row)
    {cell : Cell} (hCell : cell ∈ d.candidates)
    (hLow : sourceCell.row ≤ cell.row) (hHigh : cell.row < query) :
    cell.row ∈ d.sources.toList.map Cell.row := by
  obtain ⟨other, ho, hSegment⟩ := List.mem_flatMap.mp hCell
  rcases Nat.lt_trichotomy other.index marker.index with hBefore | hSame | hAfter
  · have hOtherBelow := d.segment_lt_marker ho hm hBefore cell hSegment
    have hMarkerBelow : (d.marker_data marker hm).current.row < sourceCell.row :=
      (d.marker_data marker hm).target_lower.trans_lt (hTarget.trans_le hCap)
    exact False.elim ((not_lt_of_ge hLow) (hOtherBelow.trans hMarkerBelow))
  · have hColumn : other.column = marker.column :=
      (d.marker_columns other ho).trans (d.marker_columns marker hm).symm
    have hRef : other = marker := by
      cases other
      cases marker
      simp only [Ref.mk.injEq]
      exact ⟨hColumn, hSame⟩
    subst other
    exact d.segment_high_row_source hm hTarget hCap hSegment hLow
  · have hOtherBelow : (d.marker_data other ho).current.row < query :=
      ((d.segment_bounds ho).2.2 cell hSegment).trans_lt hHigh
    have hOtherIndex : other.index ≤ sourceRef.index :=
      below_max_index d.source_column hSourceBelow (d.marker_data other ho).current_at hOtherBelow
    exact False.elim (hNoBetween other.index hAfter hOtherIndex (List.mem_map.mpr ⟨other, ho, rfl⟩))

/-- The copied selector preserves an inactive source-parent row using
only its own controlling cap. No cap restriction on higher markers is used. -/
theorem copyColumn_below_inactive_source (hNoPremature : NoPrematureOne d.sources)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceRef : Ref} {sourceCell : Cell}
    {query : Row} (hSourceBelow : below mountain sourceColumn query = .ok sourceRef)
    (hSource : d.sources[sourceRef.index]? = some sourceCell)
    (hIndex : marker.index ≤ sourceRef.index)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceRef.index →
      middle ∉ d.bucket.map Ref.index) {scale : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row scale)
    (hCap : Row.bump (d.marker_data marker hm).current.row scale ≤ sourceCell.row) :
    ∃ (ref : Ref) (cell : Cell), below (mountain.push column) mountain.size query = .ok ref ∧
      Canonical.cellAt (mountain.push column) ref = .ok cell ∧
      ref.column = mountain.size ∧ cell.row = sourceCell.row := by
  obtain ⟨_, selected, hSelected, hSelectedBelow⟩ := below_result d.source_column hSourceBelow
  have hSelectedEq : selected = sourceCell := Option.some.inj (hSelected.symm.trans hSource)
  have hSourceLow : sourceCell.row < query := by simpa only [hSelectedEq] using hSelectedBelow
  obtain ⟨floorIndex, floorCell, hFloor, hFloorRow⟩ :=
    finish_row_read (d.copyColumn_eq_finish.symm.trans hRun)
      (d.inactive_source_row_mem_candidates hNoPremature hm hSource hIndex hNoBetween hTarget hCap)
  have hFloorRead : Canonical.cellAt (mountain.push column) ⟨mountain.size, floorIndex⟩ = .ok floorCell :=
    cellAt_ok_iff.mpr ⟨column, by simp, hFloor⟩
  obtain ⟨actualColumn, hActualRun, _, _, _, hMountain⟩ := d.copyColumn_valid
  have hColumnEq : actualColumn = column := Except.ok.inj (hActualRun.symm.trans hRun)
  subst actualColumn
  obtain ⟨ref, cell, hBelow, hRead, hColumn, hAbove, hBound⟩ :=
    below_between hMountain hFloorRead (by simpa only [hFloorRow] using hSourceLow)
  have hSourceLe : sourceCell.row ≤ cell.row := by simpa only [hFloorRow] using hAbove
  obtain ⟨nodes, hNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  have hNodesEq : nodes = column := Option.some.inj (hNodes.symm.trans (by simp [hColumn]))
  subst nodes
  have hOutputMem : cell.row ∈ column.toList.map Cell.row := List.mem_map.mpr
    ⟨cell, List.mem_of_getElem? (by simpa only [Array.getElem?_toList] using hCell), rfl⟩
  have hCandidateMem := (finish_rows_mem_iff (d.copyColumn_eq_finish.symm.trans hRun) cell.row).mp hOutputMem
  obtain ⟨candidate, hCandidate, hCandidateRow⟩ := List.mem_map.mp hCandidateMem
  have hSourceMem := d.candidates_inactive_window_source hm hSourceBelow hNoBetween
    hTarget hCap hCandidate (by simpa only [hCandidateRow] using hSourceLe)
      (by simpa only [hCandidateRow] using hBound)
  obtain ⟨oldCell, hOldCell, hOldRow⟩ := List.mem_map.mp hSourceMem
  obtain ⟨oldIndex, hOldRead⟩ := List.mem_iff_getElem?.mp hOldCell
  have hOldArray : d.sources[oldIndex]? = some oldCell := by
    simpa only [Array.getElem?_toList] using hOldRead
  have hStrict : StrictMono (fun i : Fin d.sources.size => d.sources[i.val].row) := by
    intro i j hij
    exact d.source_valid.rows_strict _ _ _ _ (Array.getElem?_eq_getElem i.isLt)
      (Array.getElem?_eq_getElem j.isLt) hij
  have hRowEq : oldCell.row = cell.row := hOldRow.trans hCandidateRow
  have hOldLe : oldCell.row ≤ sourceCell.row := below_max_row d.source_column hStrict
    hSourceBelow hSource hOldArray (by simpa only [hRowEq] using hBound)
  exact ⟨ref, cell, hBelow, hRead, hColumn,
    le_antisymm (by simpa only [hRowEq] using hOldLe) hSourceLe⟩

/-- Ordinary parent/upper case, with actual source adjacency. The source
below success is derived here rather than supplied as a selection premise. -/
theorem copyColumn_below_inactive_adjacent (hNoPremature : NoPrematureOne d.sources)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {parent upper : Cell}
    (hParent : d.sources[sourceIndex]? = some parent)
    (hUpper : d.sources[sourceIndex + 1]? = some upper)
    (hIndex : marker.index ≤ sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex →
      middle ∉ d.bucket.map Ref.index) {scale : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row scale)
    (hCap : Row.bump (d.marker_data marker hm).current.row scale ≤ parent.row)
    {query : Row} (hLow : parent.row < query) (hHigh : query ≤ upper.row) :
    ∃ (ref : Ref) (cell : Cell), below (mountain.push column) mountain.size query = .ok ref ∧
      Canonical.cellAt (mountain.push column) ref = .ok cell ∧
      ref.column = mountain.size ∧ cell.row = parent.row := by
  exact d.copyColumn_below_inactive_source hNoPremature hRun hm
    (below_eq_of_adjacent d.ambient_valid d.source_column hParent hUpper hLow hHigh)
    hParent hIndex hNoBetween hTarget hCap

/-- A source top above its controlling cap is selected after copying for
every greater query; no artificial upper node or global last-top bound is used. -/
theorem copyColumn_below_inactive_top (hNoPremature : NoPrematureOne d.sources)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {parent : Cell}
    (hParent : d.sources[d.sources.size - 1]? = some parent)
    (hIndex : marker.index ≤ d.sources.size - 1)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ d.sources.size - 1 →
      middle ∉ d.bucket.map Ref.index) {scale : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row scale)
    (hCap : Row.bump (d.marker_data marker hm).current.row scale ≤ parent.row)
    {query : Row} (hLow : parent.row < query) :
    ∃ (ref : Ref) (cell : Cell), below (mountain.push column) mountain.size query = .ok ref ∧
      Canonical.cellAt (mountain.push column) ref = .ok cell ∧
      ref.column = mountain.size ∧ cell.row = parent.row := by
  exact d.copyColumn_below_inactive_source hNoPremature hRun hm
    (below_eq_of_top d.source_column hParent hLow) hParent hIndex hNoBetween hTarget hCap

/-- Later column appends retain the actual selected reference and read. -/
theorem copyColumn_below_inactive_source_preserved (hNoPremature : NoPrematureOne d.sources)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {later : Mountain} (hPreserve : PreservesColumns (mountain.push column) later)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceRef : Ref} {sourceCell : Cell}
    {query : Row} (hSourceBelow : below mountain sourceColumn query = .ok sourceRef)
    (hSource : d.sources[sourceRef.index]? = some sourceCell)
    (hIndex : marker.index ≤ sourceRef.index)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceRef.index →
      middle ∉ d.bucket.map Ref.index) {scale : Nat}
    (hTarget : (d.marker_data marker hm).targetCell.row <
      Row.bump (d.marker_data marker hm).current.row scale)
    (hCap : Row.bump (d.marker_data marker hm).current.row scale ≤ sourceCell.row) :
    ∃ (ref : Ref) (cell : Cell), below later mountain.size query = .ok ref ∧
      Canonical.cellAt later ref = .ok cell ∧ ref.column = mountain.size ∧ cell.row = sourceCell.row := by
  obtain ⟨ref, cell, hBelow, hRead, hColumn, hRow⟩ :=
    d.copyColumn_below_inactive_source hNoPremature hRun hm hSourceBelow hSource
      hIndex hNoBetween hTarget hCap
  obtain ⟨nodes, hNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  exact ⟨ref, cell, (hPreserve.below (by simp) query).trans hBelow,
    cellAt_ok_iff.mpr ⟨nodes, hPreserve.column_read hNodes, hCell⟩, hColumn, hRow⟩

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.inactive_source_row_mem_candidates
#print axioms OmegaY.Expansion.ColumnCopyData.candidates_inactive_window_source
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_inactive_source
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_inactive_adjacent
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_inactive_top
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_below_inactive_source_preserved
