/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SecondColumnCandidates.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.SecondSegmentControls
import OmegaY.Expansion.ColumnSegments

/-!
# The actual second-column candidates

Every segment is executed in the mountain with the first completed copy
appended. Actual descending marker order separates the complete output
segments. Candidate extraction uses the executable result, and successful
execution is proved before its default-value representation is used.
Finishing the second column remains a separate obligation.
-/

namespace OmegaY.Expansion

open Canonical

section Actual

variable {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
  {references : List Ref}
  (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
  {firstColumn : Column}
  (hCopy : copyColumn p.reduced p.marked references (p.root.column + 1)
    (p.initial.size - 1 - p.root.column) p.root.column = .ok firstColumn)
  {sources : Column}
  (hSources : (p.reduced.push firstColumn)[p.root.column + 2]? = some sources)
  (segments : Ref → List Cell)
  (hSegments : ∀ marker ∈ p.marked[p.root.column + 2]?.getD [],
    copySegment (p.reduced.push firstColumn) sources references (p.root.column + 2)
      ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker))

include hLast hMap hCopy hSources hSegments

/-- Distinct marker segments cannot share an output row. Their separating
bound is derived from the actual reference selection and source marker order. -/
theorem Preparation.second_segments_rows_nodup :
    (((p.marked[p.root.column + 2]?.getD []).flatMap segments).map Cell.row).Nodup := by
  rw [List.map_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro marker hMarker
    obtain ⟨d⟩ := p.second_segment_data hLast hMap hCopy hMarker
    have hSourcesEq : d.sources = sources := Option.some.inj (d.source_column.symm.trans hSources)
    have hRun : copySegment (p.reduced.push firstColumn) d.sources references (p.root.column + 2)
        ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker) := by
      simpa only [hSourcesEq] using hSegments marker hMarker
    exact (d.result_bounds hRun).1
  · apply (p.markers_ordered (p.root.column + 2)).1.imp_of_mem
    intro higher lower hHigher hLower hIndex
    obtain ⟨dh⟩ := p.second_segment_data hLast hMap hCopy hHigher
    obtain ⟨dl⟩ := p.second_segment_data hLast hMap hCopy hLower
    have hHigherSources : dh.sources = sources := Option.some.inj (dh.source_column.symm.trans hSources)
    have hLowerSources : dl.sources = sources := Option.some.inj (dl.source_column.symm.trans hSources)
    have hHigherRun : copySegment (p.reduced.push firstColumn) dh.sources references (p.root.column + 2)
        ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column higher.index = .ok (segments higher) := by
      simpa only [hHigherSources] using hSegments higher hHigher
    have hLowerRun : copySegment (p.reduced.push firstColumn) dl.sources references (p.root.column + 2)
        ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column lower.index = .ok (segments lower) := by
      simpa only [hLowerSources] using hSegments lower hLower
    have hNext : dl.sources[higher.index]? = some dh.current := by
      simpa only [hLowerSources, hHigherSources] using dh.current_at
    have hFloor := (dh.result_bounds hHigherRun).2.2
    have hCeiling := dl.result_lt_marker hLast hMap hLowerRun hLower hHigher hNext hIndex
    apply List.disjoint_left.mpr
    intro row hHigherRow hLowerRow
    obtain ⟨higherCell, hHigherMem, hHigherRow⟩ := List.mem_map.mp hHigherRow
    obtain ⟨lowerCell, hLowerMem, hLowerRow⟩ := List.mem_map.mp hLowerRow
    have hAtLeast := hFloor higherCell hHigherMem
    have hBelow := hCeiling lowerCell hLowerMem
    rw [hHigherRow] at hAtLeast
    rw [hLowerRow] at hBelow
    exact (not_lt_of_ge hAtLeast) hBelow

/-- Every candidate above the true bottom has an actually readable
positive-value parent in the extended ambient mountain. -/
theorem Preparation.second_segments_positive :
    ∀ cell ∈ (p.marked[p.root.column + 2]?.getD []).flatMap segments, (1 : Row) < cell.row →
      ∃ parent parentCell, cell.left = some parent ∧
        lookup (p.reduced.push firstColumn) parent = .ok parentCell ∧ 0 < parentCell.value := by
  intro cell hCell hAbove
  obtain ⟨marker, hMarker, hCell⟩ := List.mem_flatMap.mp hCell
  obtain ⟨d⟩ := p.second_segment_data hLast hMap hCopy hMarker
  have hSourcesEq : d.sources = sources := Option.some.inj (d.source_column.symm.trans hSources)
  have hRun : copySegment (p.reduced.push firstColumn) d.sources references (p.root.column + 2)
      ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker) := by
    simpa only [hSourcesEq] using hSegments marker hMarker
  exact d.result_positive hLast hMap hRun cell hCell hAbove

end Actual

/-- Actual successful first copying, reference selection, and existence of
the second source suffice to construct all candidates. Neither individual
segment success nor global row separation is assumed. -/
theorem Preparation.second_copyColumn_candidates {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {firstColumn : Column}
    (hCopy : copyColumn p.reduced p.marked references (p.root.column + 1)
      (p.initial.size - 1 - p.root.column) p.root.column = .ok firstColumn)
    (hSecond : p.root.column + 2 < p.reduced.size) :
    ∃ (sources : Column) (segments : Ref → List Cell),
      p.reduced[p.root.column + 2]? = some sources ∧
      (p.reduced.push firstColumn)[p.root.column + 2]? = some sources ∧
      (∀ marker ∈ p.marked[p.root.column + 2]?.getD [],
        copySegment (p.reduced.push firstColumn) sources references (p.root.column + 2)
          ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
          (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker) ∧
        ((segments marker).map Cell.row).Nodup) ∧
      (((p.marked[p.root.column + 2]?.getD []).flatMap segments).map Cell.row).Nodup ∧
      (∀ cell ∈ (p.marked[p.root.column + 2]?.getD []).flatMap segments, (1 : Row) < cell.row →
        ∃ parent parentCell, cell.left = some parent ∧
          lookup (p.reduced.push firstColumn) parent = .ok parentCell ∧ 0 < parentCell.value) ∧
      copyColumn (p.reduced.push firstColumn) p.marked references (p.root.column + 2)
        (p.initial.size - 1 - p.root.column) p.root.column =
        finish (p.reduced.push firstColumn) ((p.marked[p.root.column + 2]?.getD []).flatMap segments) := by
  let sources := p.reduced[p.root.column + 2]
  have hBaseSources : p.reduced[p.root.column + 2]? = some sources := Array.getElem?_eq_getElem hSecond
  have hSources := (PreservesColumns.push p.reduced firstColumn).column_read hBaseSources
  let segments : Ref → List Cell := fun marker =>
    (copySegment (p.reduced.push firstColumn) sources references (p.root.column + 2)
      ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index).toOption.getD []
  have hSegments : ∀ marker ∈ p.marked[p.root.column + 2]?.getD [],
      copySegment (p.reduced.push firstColumn) sources references (p.root.column + 2)
        ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker) ∧
      ((segments marker).map Cell.row).Nodup := by
    intro marker hMarker
    obtain ⟨d⟩ := p.second_segment_data hLast hMap hCopy hMarker
    have hSourcesEq : d.sources = sources := Option.some.inj (d.base_source_column.symm.trans hBaseSources)
    obtain ⟨result, hRun, hNodup⟩ := d.total_nodup
    rw [hSourcesEq] at hRun
    have hResult : segments marker = result := by
      simp only [segments, hRun, Except.toOption, Option.getD_some]
    exact ⟨by simpa only [hResult] using hRun, by simpa only [hResult] using hNodup⟩
  have hRuns := fun marker hMarker => (hSegments marker hMarker).1
  refine ⟨sources, segments, hBaseSources, hSources, hSegments,
    p.second_segments_rows_nodup hLast hMap hCopy hSources segments hRuns,
    p.second_segments_positive hLast hMap hCopy hSources segments hRuns, ?_⟩
  rw [p.initial_size_eq_reduced_size]
  apply copyColumn_eq_finish_segments hSources segments
  · intro marker hMarker
    exact (p.marker_iff.mp hMarker).1
  · exact hRuns

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.second_segments_rows_nodup
#print axioms OmegaY.Expansion.Preparation.second_segments_positive
#print axioms OmegaY.Expansion.Preparation.second_copyColumn_candidates
