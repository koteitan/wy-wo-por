/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SeamSourceAt.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRawCases

/-! The physical marker at a seam is copied at its original row. The
preceding endpoint, however, is the lifted source predecessor; when the
lower contour is empty this can be the fill endpoint. These statements
identify both endpoints without assuming a source pair for the seam. -/

namespace OmegaY.Expansion

open Canonical

/-- The finite contour reaches the source predecessor of the next marker.
This includes consecutive markers, for which the exponent list is empty. -/
theorem contour_source_predecessor {nodes : Column} (hPower : ColumnPowerSteps nodes)
    (hNoPremature : NoPrematureOne nodes) (markerIndices : List Nat)
    {index nextIndex : Nat} {current nextMarker : Cell}
    (hCurrent : nodes[index]? = some current) (hNext : nodes[nextIndex]? = some nextMarker)
    (hMarked : nextIndex ∈ markerIndices) (hIndex : index < nextIndex)
    (hNoBetween : ∀ middle, index < middle → middle < nextIndex → middle ∉ markerIndices)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest) :
    ∃ predecessor, nodes[nextIndex - 1]? = some predecessor ∧
      Row.run current.row (contourExponents markerIndices index current rest) = predecessor.row := by
  induction rest generalizing index current with
  | nil =>
    have hSize : nodes.size ≤ index + 1 := by
      simpa only [Array.length_toList] using List.drop_eq_nil_iff.mp hRest
    have hBound := (Array.getElem?_eq_some_iff.mp hNext).1
    omega
  | cons upper rest ih =>
    have hUpper : nodes[index + 1]? = some upper := by
      simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
        using congrArg List.head? hRest
    have hTail : nodes.toList.drop ((index + 1) + 1) = rest := by
      simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest
    by_cases hAdjacent : index + 1 = nextIndex
    · refine ⟨current, ?_, ?_⟩
      · simpa only [show nextIndex - 1 = index by omega] using hCurrent
      · have hStop : current.value = 1 ∨ index + 1 ∈ markerIndices :=
          Or.inr (hAdjacent ▸ hMarked)
        simp only [contourExponents, hStop, ↓reduceIte, Row.run_nil]
    · have hStrict : index + 1 < nextIndex := by omega
      have hStop : ¬ (current.value = 1 ∨ index + 1 ∈ markerIndices) :=
        not_or.mpr ⟨hNoPremature index current upper hCurrent hUpper,
          hNoBetween (index + 1) (by omega) hStrict⟩
      obtain ⟨predecessor, hRead, hRun⟩ := ih hUpper hStrict
        (fun middle hlo hhi => hNoBetween middle (by omega) hhi) hTail
      refine ⟨predecessor, hRead, ?_⟩
      simp only [contourExponents, hStop, ↓reduceIte, Row.run_cons]
      rw [← hPower index current upper hCurrent hUpper]
      exact hRun

section Seam

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
  {index : Nat} {lower upper : Cell} (seam : ExecutedSegmentSeam d index lower upper)
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[i]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)

include hParentPower hParentLow

theorem ExecutedSegmentSeam.upper_copy :
    copyEdge mountain ⟨sourceColumn, seam.highMarker.index⟩ shift rootColumn
      (d.marker_data seam.highMarker seam.high_member).current.row = .ok seam.originalUpper ∧
    upper.row = (d.marker_data seam.highMarker seam.high_member).current.row := by
  let md := d.marker_data seam.highMarker seam.high_member
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hParentLow seam.highMarker seam.high_member
  obtain ⟨copied, path, hCopy, _, hSegment⟩ := copySegment_sorted_splice
    d.ambient_valid d.source_column d.source_nonzero d.destination.le d.source_top
    (d.bucket.map Ref.index) md (hParentPower seam.highMarker seam.high_member)
    hLow hLowRow (d.segment_run seam.high_member)
  have hCopied : copied = seam.originalUpper := by
    have hHead := seam.upper_head
    rw [hSegment] at hHead
    exact Option.some.inj (by simpa only [List.cons_append, List.nil_append, List.head?_cons] using hHead)
  rw [hCopied] at hCopy
  exact ⟨hCopy, seam.upper_shape.1.symm.trans (copyEdge_return_row hCopy)⟩

/-- Both reads are from consecutive indices of the real source column.
The output lower may be the final fill cell or a final contour cell. -/
theorem ExecutedSegmentSeam.source_predecessor (hNoPremature : NoPrematureOne d.sources) :
    ∃ sourceLower,
      d.sources[seam.highMarker.index - 1]? = some sourceLower ∧
      d.sources[(seam.highMarker.index - 1) + 1]? =
        some (d.marker_data seam.highMarker seam.high_member).current ∧
      lower.row = Row.lift (d.marker_data seam.lowMarker seam.low_member).current.row
        (d.marker_data seam.lowMarker seam.low_member).targetCell.row sourceLower.row ∧
      upper.row = (d.marker_data seam.highMarker seam.high_member).current.row := by
  let md := d.marker_data seam.lowMarker seam.low_member
  let hd := d.marker_data seam.highMarker seam.high_member
  have hMarked : seam.highMarker.index ∈ d.bucket.map Ref.index :=
    List.mem_map.mpr ⟨seam.highMarker, seam.high_member, rfl⟩
  have hBetween : ∀ middle, seam.lowMarker.index < middle → middle < seam.highMarker.index →
      middle ∉ d.bucket.map Ref.index := by
    intro middle hLo hHi hMem
    obtain ⟨marker, hm, he⟩ := List.mem_map.mp hMem
    exact seam.no_between marker hm ⟨he ▸ hLo, he ▸ hHi⟩
  obtain ⟨sourceLower, hRead, hSourceRow⟩ := contour_source_predecessor d.source_power hNoPremature
    (d.bucket.map Ref.index) md.current_at hd.current_at hMarked seam.marker_order hBetween rfl
  have hLast := (d.sorted_segment_spec hParentPower hParentLow seam.low_member).2.2.1
  have hActualLast : (d.sortedSegmentRows seam.lowMarker).getLast? = some seam.originalLower.row := by
    simp only [ColumnCopyData.sortedSegmentRows, List.getLast?_map, seam.lower_last, Option.map_some]
  have hRunRow : seam.originalLower.row = Row.run md.targetCell.row
      (contourExponents (d.bucket.map Ref.index) seam.lowMarker.index md.current
        (d.sources.toList.drop (seam.lowMarker.index + 1))) := Option.some.inj (hActualLast.symm.trans hLast)
  have hLowerRow : lower.row = Row.lift md.current.row md.targetCell.row sourceLower.row := by
    rw [← seam.lower_shape.1, hRunRow, Row.run_eq_lift, hSourceRow]
  exact ⟨sourceLower, hRead, by
    simpa only [show seam.highMarker.index - 1 + 1 = seam.highMarker.index by
      have := seam.marker_order; omega] using hd.current_at,
    hLowerRow, (seam.upper_copy hParentPower hParentLow).2⟩

end Seam

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contour_source_predecessor
#print axioms OmegaY.Expansion.ExecutedSegmentSeam.upper_copy
#print axioms OmegaY.Expansion.ExecutedSegmentSeam.source_predecessor
