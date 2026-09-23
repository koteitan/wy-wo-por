/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialSegmentPositive.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialSegmentData
import OmegaY.Expansion.SegmentBounds
import OmegaY.Expansion.ContourPositive
import OmegaY.Expansion.FillEndpoints
import OmegaY.Expansion.FinishGeometry

/-!
# Positive parents in the actual initial copied-column candidates

The concrete first-segment data supplies every source and shifted-parent
read. Positivity is proved separately for the marker, contour, and fill.
The row-one exception is retained exactly as required by numerical backfill.
-/

namespace OmegaY.Expansion

open Canonical

theorem FirstSegmentData.current_zero_of_index_zero {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) (hIndex : marker.index = 0) : d.current.row = 0 := by
  have hRead : d.sources[0]? = some d.current := by simpa only [hIndex] using d.current_at
  have he : d.current = phantom := Option.some.inj (hRead.symm.trans d.source_valid.phantom)
  rw [he]
  rfl

theorem FirstSegmentData.index_above_one_of_row {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) (hAbove : (1 : Row) < d.current.row) :
    1 < marker.index := by
  by_contra h
  by_cases hZero : marker.index = 0
  · rw [d.current_zero_of_index_zero hZero] at hAbove
    exact (not_lt_of_ge (Row.zero_le 1)) hAbove
  · have hOne : marker.index = 1 := by omega
    have hRow : d.current.row = 1 := d.source_valid.bottom_row d.current
      (by simpa only [hOne] using d.current_at)
    rw [hRow] at hAbove
    exact (lt_irrefl (1 : Row)) hAbove

/-- The actual helper output has positive readable parents above row one.
No parent positivity or canonicality of the output is a premise. -/
theorem FirstSegmentData.segment_positive_parents {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) (hLast : 1 < last)
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {result : List Cell}
    (hRun : copySegment p.reduced d.sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result) :
    ∀ cell ∈ result, (1 : Row) < cell.row →
      ∃ parent parentCell, cell.left = some parent ∧ lookup p.reduced parent = .ok parentCell ∧
        0 < parentCell.value := by
  let indices := (p.marked[p.root.column + 1]?.getD []).map Ref.index
  obtain ⟨copied, upperPath, gap, hResult, hCopy, hCopyRow, _hZero, hContour,
    hFill, _hNodup, _hStrict, hGapBounds⟩ := copySegment_result_decomposition
      p.reduced_valid d.source_column (by omega) d.destination d.source_top references indices
      d.current_at d.upper_at d.upper_left d.parent_nodes d.target_at d.reference d.target_lower hRun
  have hCurrentRead : lookup p.reduced ⟨p.root.column + 1, marker.index⟩ = .ok d.current :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, d.current_at⟩
  have hUpperRead : lookup p.reduced ⟨p.root.column + 1, marker.index + 1⟩ = .ok d.upper :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, d.upper_at⟩
  have hAuxiliary : marker.index = 0 → d.targetCell.row = 0 := by
    intro hZero
    exact d.target_zero hLast hMap (d.current_zero_of_index_zero hZero)
  obtain ⟨positivePath, hPositivePath, _hParents, hPathPositive, _hTransport⟩ :=
    contour_total_positive p.reduced_build d.source_column (by omega) d.destination indices
      d.targetCell.row d.current_at rfl d.target_lower hAuxiliary (rootColumn := p.root.column)
  have hPathEq : positivePath = upperPath := Except.ok.inj (hPositivePath.symm.trans hContour)
  subst positivePath
  intro cell hCell hAbove
  rw [hResult] at hCell
  rcases List.mem_append.mp hCell with hFirst | hGap
  · rcases List.mem_append.mp hFirst with hMarker | hPath
    · have hCellEq : cell = copied := List.mem_singleton.mp hMarker
      subst cell
      have hCurrentAbove : (1 : Row) < d.current.row := by simpa only [hCopyRow] using hAbove
      have hIndex := d.index_above_one_of_row hCurrentAbove
      obtain ⟨oldParent, oldParentCell, hOldLeft, hOldRead, hOldPositive, _, _, _⟩ :=
        build_above_bottom_stored_parent p.reduced_build d.current_read hIndex
      obtain ⟨positiveCopy, parent, parentCell, hPositiveCopy, _hRow, _hValue,
        hLeft, hParent, _hParentColumn, hParentPositive⟩ :=
        copyEdge_positive_parent p.reduced_valid hCurrentRead
          (show 0 < (⟨p.root.column + 1, marker.index⟩ : Ref).column by change 0 < p.root.column + 1; omega)
          d.destination
          (ne_of_gt (Row.zero_lt_one.trans hCurrentAbove)) hCurrentAbove hOldLeft
          (lookup_ok_iff.mpr (cellAt_ok_iff.mp hOldRead)) hOldPositive (rootColumn := p.root.column)
      have he : positiveCopy = copied := Except.ok.inj (hPositiveCopy.symm.trans hCopy)
      subst positiveCopy
      exact ⟨parent, parentCell, hLeft, hParent, hParentPositive⟩
    · obtain ⟨parent, parentCell, hLeft, hParent, hPositive, _⟩ := hPathPositive cell hPath hAbove
      exact ⟨parent, parentCell, hLeft, hParent, hPositive⟩
  · by_cases hZero : d.current.row = 0
    · have hTargetZero := d.target_zero hLast hMap hZero
      obtain ⟨hLow, hHigh⟩ := hGapBounds cell hGap
      rw [hZero] at hLow
      rw [hTargetZero] at hHigh
      exact False.elim ((not_lt_of_ge hHigh) hLow)
    · obtain ⟨hc, hParentNodes⟩ := Array.getElem?_eq_some_iff.mp d.parent_nodes
      have hParentValid : ColumnValid p.reduced
          (d.sourceParent.column + (p.reduced.size - 1 - p.root.column)) d.parentNodes :=
        hParentNodes ▸ p.reduced_valid _ hc
      have hLeftward : d.sourceParent.column < p.root.column + 1 :=
        (d.source_valid.stored_valid _ _ _ d.upper_at d.upper_left).1
      obtain ⟨positiveGap, hPositiveGap, hGapPositive⟩ :=
        fill_with_positive_parents hUpperRead d.upper_left d.parent_nodes hParentValid
          d.target_at le_rfl (row_one_le_of_ne_zero hZero) hLeftward
          (high := d.targetCell.row)
      have he : positiveGap = gap := Except.ok.inj (hPositiveGap.symm.trans hFill)
      subst positiveGap
      obtain ⟨parent, parentCell, hLeft, hParent, _hIndex, hPositive⟩ := hGapPositive cell hGap
      exact ⟨parent, parentCell, hLeft, hParent, hPositive⟩

theorem Preparation.initial_segment_positive_parents {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {sources : Column} (hSources : p.reduced[p.root.column + 1]? = some sources)
    {marker : Ref} (hMarker : BucketMem p.marked (p.root.column + 1) marker)
    {result : List Cell}
    (hRun : copySegment p.reduced sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result) :
    ∀ cell ∈ result, (1 : Row) < cell.row →
      ∃ parent parentCell, cell.left = some parent ∧ lookup p.reduced parent = .ok parentCell ∧
        0 < parentCell.value := by
  obtain ⟨d⟩ := p.first_segment_data hLast hMap hMarker
  have he : sources = d.sources := Option.some.inj (hSources.symm.trans d.source_column)
  subst sources
  exact d.segment_positive_parents hLast hMap hRun

/-- Positivity for the exact unsorted candidate concatenation used by the
original column loop. Every segment premise is an actual execution equation. -/
theorem Preparation.initial_candidates_positive_parents {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {sources : Column} (hSources : p.reduced[p.root.column + 1]? = some sources)
    (segments : Ref → List Cell)
    (hSegments : ∀ marker ∈ p.marked[p.root.column + 1]?.getD [],
      copySegment p.reduced sources references (p.root.column + 1)
        ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker)) :
    ∀ cell ∈ (p.marked[p.root.column + 1]?.getD []).flatMap segments, (1 : Row) < cell.row →
      ∃ parent parentCell, cell.left = some parent ∧ lookup p.reduced parent = .ok parentCell ∧
        0 < parentCell.value := by
  intro cell hCell hAbove
  obtain ⟨marker, hMarker, hMember⟩ := List.mem_flatMap.mp hCell
  exact p.initial_segment_positive_parents hLast hMap hSources hMarker
    (hSegments marker hMarker) cell hMember hAbove

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_segment_positive_parents
#print axioms OmegaY.Expansion.Preparation.initial_candidates_positive_parents
