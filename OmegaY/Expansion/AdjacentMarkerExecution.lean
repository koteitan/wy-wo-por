/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/AdjacentMarkerExecution.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveCopy
import OmegaY.Expansion.SeamSourceAt

/-!
# Forward execution at the next physical marker

The ordered marker bucket and the real sorted segment endpoints construct
the output adjacency. No output-adjacency or executed-seam premise is used.
The next marker is copied at its original row, even when the preceding
effective occurrence is lifted. Consecutive markers are included.
-/

namespace OmegaY.Expansion

open Canonical

private theorem ordered_marker_split {markers : List Ref} {low high : Ref}
    (hOrder : markers.Pairwise (fun a b => a.index < b.index))
    (hLow : low ∈ markers) (hHigh : high ∈ markers) (hLt : low.index < high.index)
    (hBetween : ∀ marker ∈ markers, ¬ (low.index < marker.index ∧ marker.index < high.index)) :
    ∃ before after, markers = before ++ low :: high :: after := by
  classical
  induction markers with
  | nil => simp at hLow
  | cons first rest ih =>
    have hParts := List.pairwise_cons.mp hOrder
    by_cases he : first = low
    · subst first
      have hHighRest : high ∈ rest := by
        rcases List.mem_cons.mp hHigh with he | hm
        · subst high; omega
        · exact hm
      cases rest with
      | nil => simp at hHighRest
      | cons second tail =>
        by_cases he : second = high
        · subst second
          exact ⟨[], tail, rfl⟩
        · have hHighTail : high ∈ tail := by
            rcases List.mem_cons.mp hHighRest with heq | hm
            · exact False.elim (he heq.symm)
            · exact hm
          exact False.elim (hBetween second (by simp)
            ⟨hParts.1 second (by simp), (List.pairwise_cons.mp hParts.2).1 high hHighTail⟩)
    · have hLowRest : low ∈ rest := by
        rcases List.mem_cons.mp hLow with heq | hm
        · exact False.elim (he heq.symm)
        · exact hm
      have hHighRest : high ∈ rest := by
        rcases List.mem_cons.mp hHigh with heq | hm
        · have hBefore := hParts.1 low hLowRest
          rw [← heq] at hBefore
          omega
        · exact hm
      obtain ⟨before, after, hSplit⟩ := ih hParts.2 hLowRest hHighRest
        (fun marker hm => hBetween marker (List.mem_cons_of_mem first hm))
      exact ⟨first :: before, after, by simp only [List.cons_append, hSplit]⟩

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)

include hParentPower hParentLow hNoPremature

/-- A source-marker gap constructs a real seam at a newly determined output
index. In particular the returned execution certificate is a conclusion. -/
theorem copyColumn_adjacent_marker_execution {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {low high : Ref} (hLow : low ∈ d.bucket) (hHigh : high ∈ d.bucket)
    (hLt : low.index < high.index)
    (hBetween : ∀ marker ∈ d.bucket, ¬ (low.index < marker.index ∧ marker.index < high.index)) :
    ∃ (index : Nat) (lower upper : Cell) (seam : ExecutedSegmentSeam d index lower upper),
      column[index]? = some lower ∧ column[index + 1]? = some upper ∧
      seam.lowMarker = low ∧ seam.highMarker = high := by
  obtain ⟨before, after, hSplit⟩ := ordered_marker_split
    (List.pairwise_reverse.mpr d.marker_order) (List.mem_reverse.mpr hLow)
    (List.mem_reverse.mpr hHigh) hLt
    (fun marker hm => hBetween marker (List.mem_reverse.mp hm))
  have hLast := (d.sorted_segment_spec hParentPower hParentLow hLow).2.2.1
  have hHead := (d.sorted_segment_spec hParentPower hParentLow hHigh).2.1
  simp only [sortedSegmentRows, List.getLast?_map] at hLast
  simp only [sortedSegmentRows, List.head?_map] at hHead
  obtain ⟨originalLower, hOriginalLower, _⟩ := Option.map_eq_some_iff.mp hLast
  obtain ⟨originalUpper, hOriginalUpper, _⟩ := Option.map_eq_some_iff.mp hHead
  obtain ⟨lowPrefix, hLowSplit⟩ := List.getLast?_eq_some_iff.mp hOriginalLower
  obtain ⟨highTail, hHighSplit⟩ := List.head?_eq_some_iff.mp hOriginalUpper
  let pieces := fun marker => finishSort (d.segment marker)
  let beforeCells := before.flatMap pieces ++ lowPrefix
  have hSorted : finishSort d.candidates =
      beforeCells ++ [originalLower, originalUpper] ++ (highTail ++ after.flatMap pieces) := by
    rw [d.finishSort_candidates_cells hParentPower hParentLow hNoPremature]
    simp only [ascendingCells, hSplit, List.flatMap_append, List.flatMap_cons,
      hLowSplit, hHighSplit, beforeCells, pieces, List.append_assoc, List.cons_append,
      List.nil_append]
  obtain ⟨lower, upper, hLower, hUpper, hLowerShape, hUpperShape⟩ :=
    finish_adjacent_of_splice (d.copyColumn_eq_finish.symm.trans hRun) hSorted
      (show ([originalLower, originalUpper] : List Cell)[0]? = some originalLower by rfl)
      (show ([originalLower, originalUpper] : List Cell)[0 + 1]? = some originalUpper by rfl)
  let seam : ExecutedSegmentSeam d beforeCells.length lower upper := {
    lowMarker := low
    highMarker := high
    low_member := hLow
    high_member := hHigh
    before := before
    after := after
    originalLower := originalLower
    originalUpper := originalUpper
    bucket_split := hSplit
    marker_order := hLt
    no_between := hBetween
    position := by simp [beforeCells, pieces, hLowSplit]
    lower_last := hOriginalLower
    upper_head := hOriginalUpper
    lower_shape := hLowerShape
    upper_shape := hUpperShape }
  exact ⟨beforeCells.length, lower, upper, seam,
    by simpa only [Nat.add_zero] using hLower,
    by simpa only [Nat.add_zero] using hUpper, rfl, rfl⟩

/-- The actual successor of an effective occurrence immediately below a
marked source node is the physical copy of that marked node. The theorem
also covers consecutive markers, with the low effective target ending its
fill. Values are not identified across numerical backfill. -/
theorem effective_upper_marker_execution {column : Column} {sourceIndex : Nat}
    {sourceLower sourceUpper : Cell} (read : EffectiveCopyRead d sourceIndex sourceLower column)
    (hUpper : d.sources[sourceIndex + 1]? = some sourceUpper)
    (hMarked : sourceIndex + 1 ∈ d.bucket.map Ref.index) :
    ∃ upper copied,
      column[read.outputIndex + 1]? = some upper ∧ upper.row = sourceUpper.row ∧
      copyEdge mountain ⟨sourceColumn, sourceIndex + 1⟩ shift rootColumn sourceUpper.row = .ok copied ∧
      SameShape copied upper := by
  obtain ⟨high, hHigh, hHighIndex⟩ := List.mem_map.mp hMarked
  have hLt : read.marker.index < high.index := by have := read.marker_before; omega
  have hBetween : ∀ marker ∈ d.bucket,
      ¬ (read.marker.index < marker.index ∧ marker.index < high.index) := by
    intro marker hm hRange
    exact read.no_between marker.index hRange.1 (by omega) (List.mem_map.mpr ⟨marker, hm, rfl⟩)
  obtain ⟨position, lower, upper, seam, hLower, hOutputUpper, hLowMarker, hHighMarker⟩ :=
    d.copyColumn_adjacent_marker_execution hParentPower hParentLow hNoPremature
      read.copy_run read.marker_mem hHigh hLt hBetween
  obtain ⟨predecessor, hPredecessor, _, hLowerRow, hUpperRow⟩ :=
    seam.source_predecessor hParentPower hParentLow hNoPremature
  have hPredecessorEq : predecessor = sourceLower := Option.some.inj
    (hPredecessor.symm.trans (by simpa only [hHighMarker, hHighIndex, Nat.add_sub_cancel] using read.source_at))
  have hCurrentEq : (d.marker_data seam.highMarker seam.high_member).current = sourceUpper :=
    Option.some.inj ((d.marker_data seam.highMarker seam.high_member).current_at.symm.trans
      (by simpa only [hHighMarker, hHighIndex] using hUpper))
  have hLowCurrent : (d.marker_data seam.lowMarker seam.low_member).current =
      (d.marker_data read.marker read.marker_mem).current := Option.some.inj
    ((d.marker_data seam.lowMarker seam.low_member).current_at.symm.trans
      (by simpa only [hLowMarker] using (d.marker_data read.marker read.marker_mem).current_at))
  have hLowTarget : (d.marker_data seam.lowMarker seam.low_member).targetCell.row =
      (d.marker_data read.marker read.marker_mem).targetCell.row := by
    have hReference := (d.marker_data seam.lowMarker seam.low_member).reference
    rw [hLowCurrent] at hReference
    exact Except.ok.inj (hReference.symm.trans (d.marker_data read.marker read.marker_mem).reference)
  have hLowRow : lower.row = read.outputCell.row := by
    simpa only [hLowCurrent, hLowTarget, hPredecessorEq, read.output_row] using hLowerRow
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans read.copy_run)
  subst actual
  have hPosition : position = read.outputIndex :=
    column_read_index_eq_of_row hValid hLower read.output_at hLowRow
  refine ⟨upper, seam.originalUpper, ?_, hUpperRow.trans (congrArg Cell.row hCurrentEq), ?_, seam.upper_shape⟩
  · simpa only [hPosition] using hOutputUpper
  · simpa only [hHighMarker, hHighIndex, hCurrentEq] using
      (seam.upper_copy hParentPower hParentLow).1

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_adjacent_marker_execution
#print axioms OmegaY.Expansion.ColumnCopyData.effective_upper_marker_execution
