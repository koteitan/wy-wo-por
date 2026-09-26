/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SecondBaseRows.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.SecondSegmentControls

/-! Actual phantom and bottom-row occurrence in the second column's
candidate list. The ambient mountain already includes the first copy. -/

namespace OmegaY.Expansion

open Canonical

section Candidates

variable {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
  {references : List Ref}
  (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
  {firstColumn : Column}
  (hCopy : copyColumn p.reduced p.marked references (p.root.column + 1)
    (p.initial.size - 1 - p.root.column) p.root.column = .ok firstColumn)
  {sources : Column} (hSources : p.reduced[p.root.column + 2]? = some sources)
  (segments : Ref → List Cell)
  (hSegments : ∀ marker ∈ p.marked[p.root.column + 2]?.getD [],
    copySegment (p.reduced.push firstColumn) sources references (p.root.column + 2)
      ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker))

include hLast hMap hCopy hSources hSegments

theorem Preparation.second_candidates_phantom :
    phantom ∈ (p.marked[p.root.column + 2]?.getD []).flatMap segments := by
  have hc := (Array.getElem?_eq_some_iff.mp hSources).1
  have hMarker := p.phantom_marker (show p.root.column < p.root.column + 2 by omega) hc
  let marker : Ref := ⟨p.root.column + 2, 0⟩
  obtain ⟨d⟩ := p.second_segment_data hLast hMap hCopy hMarker
  have hSourceEq : d.sources = sources := Option.some.inj (d.base_source_column.symm.trans hSources)
  have hCurrentEq : d.current = phantom :=
    Option.some.inj (d.current_at.symm.trans d.source_valid.phantom)
  have hRun := hSegments marker hMarker
  rw [← hSourceEq] at hRun
  obtain ⟨copied, path, gap, hResult, hCopied, _, _, _, _, _, _, _⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column (by omega) d.destination
      d.source_top references _ d.current_at d.upper_at d.upper_left d.parent_nodes
      d.target_at d.reference d.target_lower hRun
  have hPhantomRead : lookup (p.reduced.push firstColumn) ⟨p.root.column + 2, 0⟩ = .ok phantom :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, d.source_valid.phantom⟩
  have hCopyPhantom : copied = phantom := by
    rw [hCurrentEq] at hCopied
    exact Except.ok.inj (hCopied.symm.trans (copyEdge_phantom hPhantomRead rfl _ _ 0))
  apply List.mem_flatMap.mpr
  exact ⟨marker, hMarker, by rw [hResult, hCopyPhantom]; simp⟩

theorem Preparation.second_candidates_one :
    (1 : Row) ∈ ((p.marked[p.root.column + 2]?.getD []).flatMap segments).map Cell.row := by
  obtain ⟨hc, hSourcesEq⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hCV : ColumnValid p.reduced (p.root.column + 2) sources :=
    hSourcesEq ▸ p.reduced_valid _ hc
  have hSize := hCV.size_ge_two
  have hb : 1 < sources.size := by omega
  let bottom := sources[1]
  let bottomRef : Ref := ⟨p.root.column + 2, 1⟩
  have hBottom : sources[1]? = some bottom := Array.getElem?_eq_getElem hb
  have hBottomRow := hCV.bottom_row bottom hBottom
  by_cases hBottomMarker : BucketMem p.marked (p.root.column + 2) bottomRef
  · obtain ⟨d⟩ := p.second_segment_data hLast hMap hCopy hBottomMarker
    have hSourceEq : d.sources = sources := Option.some.inj (d.base_source_column.symm.trans hSources)
    have hCurrentEq : d.current = bottom := by
      have hRead := d.current_at
      rw [hSourceEq] at hRead
      exact Option.some.inj (hRead.symm.trans hBottom)
    have hRun := hSegments bottomRef hBottomMarker
    rw [← hSourceEq] at hRun
    have hMember := (d.result_bounds hRun).2.1
    obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hMember
    exact List.mem_map.mpr ⟨cell, List.mem_flatMap.mpr ⟨bottomRef, hBottomMarker, hCell⟩,
      hRow.trans ((congrArg Cell.row hCurrentEq).trans hBottomRow)⟩
  · have hNotMarked : 1 ∉ (p.marked[p.root.column + 2]?.getD []).map Ref.index := by
      intro hm
      obtain ⟨entry, hEntry, hIndex⟩ := List.mem_map.mp hm
      have hColumn := (p.marker_iff.mp hEntry).1
      have he : entry = bottomRef := by
        cases entry
        simp_all only [bottomRef]
      exact hBottomMarker (he ▸ hEntry)
    have hMarker := p.phantom_marker (show p.root.column < p.root.column + 2 by omega) hc
    let marker : Ref := ⟨p.root.column + 2, 0⟩
    obtain ⟨d⟩ := p.second_segment_data hLast hMap hCopy hMarker
    have hSourceEq : d.sources = sources := Option.some.inj (d.base_source_column.symm.trans hSources)
    have hCurrentEq : d.current = phantom :=
      Option.some.inj (d.current_at.symm.trans d.source_valid.phantom)
    have hZero : d.targetCell.row = 0 := d.target_zero hLast hMap (congrArg Cell.row hCurrentEq)
    have hRun := hSegments marker hMarker
    rw [← hSourceEq] at hRun
    obtain ⟨copied, path, gap, hResult, _, _, _, hContour, _, _, _, _⟩ :=
      copySegment_result_decomposition d.ambient_valid d.source_column (by omega) d.destination
        d.source_top references _ d.current_at d.upper_at d.upper_left d.parent_nodes
        d.target_at d.reference d.target_lower hRun
    rw [hCurrentEq, hZero] at hContour
    have hOne := contour_phantom_contains_one d.ambient_valid d.source_column (by omega)
      d.destination d.source_top _ hNotMarked hContour
    obtain ⟨cell, hCell, hRow⟩ := List.mem_map.mp hOne
    apply List.mem_map.mpr
    refine ⟨cell, List.mem_flatMap.mpr ⟨marker, hMarker, ?_⟩, hRow⟩
    rw [hResult]
    simp [hCell]

end Candidates

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.second_candidates_phantom
#print axioms OmegaY.Expansion.Preparation.second_candidates_one
