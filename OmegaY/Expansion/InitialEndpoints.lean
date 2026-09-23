/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialEndpoints.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialValid
import OmegaY.Expansion.FinishSupport

/-! The first copied column retains both each actual marker row and its
selected reference target. A lifted target is supplied by the real fill
endpoint, not by pretending it is the unlifted marker. -/

namespace OmegaY.Expansion

open Canonical

theorem FirstSegmentData.lower_parent_read {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) (hLast : 1 < last)
    (hMarker : BucketMem p.marked (p.root.column + 1) marker) :
    ∃ (index : Nat) (cell : Cell), d.parentNodes[index]? = some cell ∧ cell.row = d.current.row := by
  obtain ⟨nodes, index, lower, hColumn, hLower, hIndex, hRow⟩ :=
    p.marker_root_prefix_read hMarker d.current_read
  obtain ⟨ref, cell, hRead, hRefColumn, hCellRow⟩ :=
    p.reduced_root_prefix_read hLast hColumn hLower hIndex
  have hs := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hs
  have hr := p.root_before_last
  have hShift : d.sourceParent.column + (p.reduced.size - 1 - p.root.column) =
      p.reduced.size - 1 := by rw [d.parent_column]; omega
  obtain ⟨parentNodes, hParentNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  have hNodesEq : parentNodes = d.parentNodes := by
    apply Option.some.inj
    exact hParentNodes.symm.trans (by simpa only [hRefColumn, hShift] using d.parent_nodes)
  subst parentNodes
  exact ⟨ref.index, cell, hCell, hCellRow.trans hRow⟩

/-- Every selected target actually occurs in its first-column segment. If
the target equals the marker, use the marker; otherwise use the last gap
ladder's endpoint in the canonical boundary parent column. -/
theorem FirstSegmentData.segment_target_mem {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) (hLast : 1 < last)
    (hMarker : BucketMem p.marked (p.root.column + 1) marker) {result : List Cell}
    (hRun : copySegment p.reduced d.sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result) :
    d.targetCell.row ∈ result.map Cell.row := by
  obtain ⟨copied, upperPath, gap, hResult, _, hCopyRow, _, _, hFill, _, _, _⟩ :=
    copySegment_result_decomposition p.reduced_valid d.source_column (by omega)
      d.destination d.source_top references _ d.current_at d.upper_at d.upper_left
      d.parent_nodes d.target_at d.reference d.target_lower hRun
  rcases eq_or_lt_of_le d.target_lower with hEqual | hStrict
  · rw [hResult]
    exact List.mem_map.mpr ⟨copied, by simp, hCopyRow.trans hEqual⟩
  · obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := d.lower_parent_read hLast hMarker
    obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp d.parent_nodes
    have hParentValid : ColumnValid p.reduced
        (d.sourceParent.column + (p.reduced.size - 1 - p.root.column)) d.parentNodes :=
      hNodes ▸ p.reduced_valid _ hc
    have hPower := build_column_power_steps_of_read p.reduced_build d.parent_nodes
    have hUpperRead : lookup p.reduced ⟨p.root.column + 1, marker.index + 1⟩ = .ok d.upper :=
      lookup_ok_iff.mpr ⟨d.sources, d.source_column, d.upper_at⟩
    have hLeftward := (d.source_valid.stored_valid _ _ _ d.upper_at d.upper_left).1
    obtain ⟨filled, hFilled, _, _, hHigh, _⟩ := fill_spec_with_high
      hUpperRead d.upper_left d.parent_nodes hParentValid hPower hLow d.target_at
      (by simpa only [hLowRow] using hStrict) hLeftward
    rw [hLowRow] at hFilled
    have he : filled = gap := Except.ok.inj (hFilled.symm.trans hFill)
    rw [he] at hHigh
    obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hHigh
    rw [hResult]
    exact List.mem_map.mpr ⟨cell, List.mem_append_right _ hCell, hRow⟩

/-- Both heights survive the actual unsorted candidate list, real sorting,
and numerical backfill. Output indices are freshly witnessed. -/
theorem Preparation.initial_copyColumn_marker_target_reads {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {column : Column}
    (hCopy : copyColumn p.reduced p.marked references (p.root.column + 1)
      (p.initial.size - 1 - p.root.column) p.root.column = .ok column)
    {marker : Ref} (hMarker : BucketMem p.marked (p.root.column + 1) marker)
    {source : Cell} (hSource : Canonical.cellAt p.reduced marker = .ok source)
    {target : Row} (hTarget : referenceAt p.reduced references source.row = .ok target) :
    (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ cell.row = source.row) ∧
    (∃ (index : Nat) (cell : Cell), column[index]? = some cell ∧ cell.row = target) := by
  obtain ⟨otherReferences, sources, segments, hOtherMap, hSources, hSegments, _, hColumn⟩ :=
    p.initial_copyColumn_candidates_nodup hLast
  have hRefsEq : otherReferences = references := Except.ok.inj (hOtherMap.symm.trans hMap)
  subst otherReferences
  have hCopyReduced := hCopy
  rw [p.initial_size_eq_reduced_size] at hCopyReduced
  have hFinish := hColumn.symm.trans hCopyReduced
  obtain ⟨d⟩ := p.first_segment_data hLast hMap hMarker
  have hSourcesEq : sources = d.sources := Option.some.inj (hSources.symm.trans d.source_column)
  subst sources
  have hSourceEq : source = d.current := Except.ok.inj (hSource.symm.trans d.current_read)
  subst source
  have hTargetEq : target = d.targetCell.row := Except.ok.inj (hTarget.symm.trans d.reference)
  subst target
  have hRun := (hSegments marker hMarker).1
  have hMarkerMem := (copySegment_result_bounds p.reduced_valid d.source_column (by omega)
    d.destination d.source_top references _ d.current_at d.upper_at d.upper_left
    d.parent_nodes d.target_at d.reference d.target_lower hRun).2.1
  have hTargetMem := d.segment_target_mem hLast hMarker hRun
  have hEmbed : ∀ row ∈ (segments marker).map Cell.row,
      row ∈ ((p.marked[p.root.column + 1]?.getD []).flatMap segments).map Cell.row := by
    intro row hRow
    obtain ⟨cell, hCell, hCellRow⟩ := List.mem_map.mp hRow
    exact List.mem_map.mpr ⟨cell, List.mem_flatMap.mpr ⟨marker, hMarker, hCell⟩, hCellRow⟩
  exact ⟨finish_row_read hFinish (hEmbed _ hMarkerMem),
    finish_row_read hFinish (hEmbed _ hTargetMem)⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.FirstSegmentData.segment_target_mem
#print axioms OmegaY.Expansion.Preparation.initial_copyColumn_marker_target_reads
