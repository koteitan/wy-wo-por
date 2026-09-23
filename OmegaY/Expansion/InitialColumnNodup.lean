/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialColumnNodup.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialSegmentBounds
import OmegaY.Expansion.InitialColumn

/-!
# No overlapping rows in the first actual copied column

Prepared markers occur in strictly descending index order. Each lower
marker's entire segment lies below the higher marker, while the higher
segment lies at or above its own marker. Hence the original executable
concatenation is free of repeated rows, without sorting or discarding cells.
-/

namespace OmegaY.Expansion

open Canonical

/-- No cross-segment separation is an input: it follows from the actual
marker order and the derived initial reference intervals. -/
theorem Preparation.initial_segments_rows_nodup {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {sources : Column} (hSources : p.reduced[p.root.column + 1]? = some sources)
    (segments : Ref → List Cell)
    (hSegments : ∀ marker ∈ p.marked[p.root.column + 1]?.getD [],
      copySegment p.reduced sources references (p.root.column + 1)
        ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker)) :
    (((p.marked[p.root.column + 1]?.getD []).flatMap segments).map Cell.row).Nodup := by
  rw [List.map_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro marker hMarker
    obtain ⟨current, hCurrent, _⟩ := p.marker_cell_row_bound hMarker
    exact (p.initial_segment_result_bounds hLast hMap hSources hMarker hCurrent
      (hSegments marker hMarker)).1
  · apply (p.markers_ordered (p.root.column + 1)).1.imp_of_mem
    intro higher lower hHigher hLower hIndex
    apply List.disjoint_left.mpr
    intro row hHigherRow hLowerRow
    obtain ⟨higherCell, hHigherRead, _⟩ := p.marker_cell_row_bound hHigher
    have hFloor := (p.initial_segment_result_bounds hLast hMap hSources hHigher hHigherRead
      (hSegments higher hHigher)).2.2
    have hCeiling := p.initial_segment_result_lt_marker hLast hMap hSources hLower
      (hSegments lower hLower) hHigher hHigherRead hIndex
    obtain ⟨upperCell, hUpperMem, hUpperRow⟩ := List.mem_map.mp hHigherRow
    obtain ⟨lowerCell, hLowerMem, hLowerRow⟩ := List.mem_map.mp hLowerRow
    have hAtLeast := hFloor upperCell hUpperMem
    have hBelow := hCeiling lowerCell hLowerMem
    rw [hUpperRow] at hAtLeast
    rw [hLowerRow] at hBelow
    exact (not_lt_of_ge hAtLeast) hBelow

/-- Preparation alone produces references, all successful segments, global
row non-overlap, and the exact original `copyColumn = finish` equation.
Numerical finishing remains visible as a separate operation. -/
theorem Preparation.initial_copyColumn_candidates_nodup {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) :
    ∃ (references : List Ref) (sources : Column) (segments : Ref → List Cell),
      p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references ∧
      p.reduced[p.root.column + 1]? = some sources ∧
      (∀ marker ∈ p.marked[p.root.column + 1]?.getD [],
        copySegment p.reduced sources references (p.root.column + 1)
          ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
          (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker) ∧
        ((segments marker).map Cell.row).Nodup) ∧
      (((p.marked[p.root.column + 1]?.getD []).flatMap segments).map Cell.row).Nodup ∧
      copyColumn p.reduced p.marked references (p.root.column + 1)
        (p.reduced.size - 1 - p.root.column) p.root.column =
        finish p.reduced ((p.marked[p.root.column + 1]?.getD []).flatMap segments) := by
  obtain ⟨references, sources, segments, hMap, hSources, hSegments, hColumn⟩ :=
    p.initial_copyColumn_candidates hLast
  exact ⟨references, sources, segments, hMap, hSources, hSegments,
    p.initial_segments_rows_nodup hLast hMap hSources segments
      (fun marker hMarker => (hSegments marker hMarker).1), hColumn⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_segments_rows_nodup
#print axioms OmegaY.Expansion.Preparation.initial_copyColumn_candidates_nodup
