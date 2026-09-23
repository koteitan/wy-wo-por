/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialColumn.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialSegment
import OmegaY.Expansion.ColumnSegments

/-! All marker segments of the first copied column are constructed, and
their actual concatenation is passed to the original executable finish.
Finishing and separation between distinct marker segments remain unproved. -/

namespace OmegaY.Expansion

open Canonical

/-- No segment-success or target-support condition is an input here.
Every segment is obtained from the real prepared graph and reference map.
The concluding equality deliberately preserves `finish` as an obligation. -/
theorem Preparation.initial_copyColumn_candidates {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) :
    ∃ (references : List Ref) (sources : Column) (segments : Ref → List Cell),
      p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references ∧
      p.reduced[p.root.column + 1]? = some sources ∧
      (∀ marker ∈ p.marked[p.root.column + 1]?.getD [],
        copySegment p.reduced sources references (p.root.column + 1)
          ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
          (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker) ∧
        ((segments marker).map Cell.row).Nodup) ∧
      copyColumn p.reduced p.marked references (p.root.column + 1)
        (p.reduced.size - 1 - p.root.column) p.root.column =
        finish p.reduced ((p.marked[p.root.column + 1]?.getD []).flatMap segments) := by
  obtain ⟨references, hMap, _⟩ := p.initial_references hLast
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRootLeft := p.root_before_last
  have hc : p.root.column + 1 < p.reduced.size := by omega
  let sources := p.reduced[p.root.column + 1]
  have hSources : p.reduced[p.root.column + 1]? = some sources := Array.getElem?_eq_getElem hc
  let segments : Ref → List Cell := fun marker =>
    (copySegment p.reduced sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index).toOption.getD []
  have hSegments : ∀ marker ∈ p.marked[p.root.column + 1]?.getD [],
      copySegment p.reduced sources references (p.root.column + 1)
        ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker) ∧
      ((segments marker).map Cell.row).Nodup := by
    intro marker hMarker
    obtain ⟨otherSources, result, hOtherSources, hRun, hNodup⟩ :=
      p.initial_segment_total_nodup hLast hMap hMarker
    have he : otherSources = sources := Option.some.inj (hOtherSources.symm.trans hSources)
    subst otherSources
    have hResult : segments marker = result := by simp only [segments, hRun, Except.toOption, Option.getD_some]
    exact ⟨by simpa only [hResult] using hRun, by simpa only [hResult] using hNodup⟩
  refine ⟨references, sources, segments, hMap, hSources, hSegments, ?_⟩
  apply copyColumn_eq_finish_segments hSources segments
  · intro marker hMarker
    exact (p.marker_iff.mp hMarker).1
  · intro marker hMarker
    exact (hSegments marker hMarker).1

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_copyColumn_candidates
