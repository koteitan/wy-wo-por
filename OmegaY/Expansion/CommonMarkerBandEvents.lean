/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonMarkerBandEvents.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CommonMarkerBands
import OmegaY.Expansion.RawNumericSuffix
import OmegaY.Expansion.ActualIntervalEdge

/-!+# Every inserted event in two actual common marker bands

The two finished bands have the same complete ascending fill. At every
cut from the physical-marker row up to but excluding the effective-target
row, a finite maximum chooses the same band offset in both columns. Their
actual upper-stored references agree, so their raw event parents and depths
agree. This covers all inserted events in the band, not just its endpoints.
No target numerical-parent recognition, Normal or raw-B assumption is used.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem MarkerBand.offset_read {mountain : Mountain} {columnIndex : Nat}
    {nodes : Column} {gap : List Cell} {low high : Row}
    (band : MarkerBand nodes gap low high)
    (hColumn : mountain[columnIndex]? = some nodes) {offset : Nat} (hOffset : offset ≤ gap.length) :
    Canonical.cellAt mountain ⟨columnIndex, band.start + offset⟩ =
      .ok (nodes[band.start + offset]?.getD phantom) := by
  have hb : band.start + offset < nodes.size := by have := band.bound; omega
  apply cellAt_ok_iff.mpr
  refine ⟨nodes, hColumn, ?_⟩
  simp only [Array.getElem?_eq_getElem hb, Option.getD_some]

theorem CommonMarkerBandPair.rows_agree {left right : Column} {low high : Row}
    (pair : CommonMarkerBandPair left right low high) {offset : Nat}
    (hOffset : offset ≤ pair.gap.length) :
    (left[pair.leftBand.start + offset]?.getD phantom).row =
      (right[pair.rightBand.start + offset]?.getD phantom).row := by
  cases offset with
  | zero => simpa only [Nat.add_zero] using pair.leftBand.low_row.trans pair.rightBand.low_row.symm
  | succ offset =>
      have hi : offset < pair.gap.length := by omega
      exact (pair.leftBand.upper_shape offset hi).1.symm.trans (pair.rightBand.upper_shape offset hi).1

/-- All target cuts in the half-open physical/effective interval are
covered. The maximum index and all actual endpoint reads are built from
the finite band; no target-frontier hypothesis is supplied. -/
theorem CommonMarkerBandPair.frontierAt_rawParent_eq
    {mountain : Mountain} (hValid : MountainValid mountain)
    {left right : Column} {low high : Row} (pair : CommonMarkerBandPair left right low high)
    (leftColumn rightColumn : Fin (Frame.ofMountain mountain).width)
    (hLeft : mountain[leftColumn.val]? = some left)
    (hRight : mountain[rightColumn.val]? = some right)
    {cut : Row} (hCut : (1 : Row) ≤ cut) (hLow : low ≤ cut) (hHigh : cut < high) :
    (Frame.ofMountain mountain).rawParent (frontierAt hValid.toOrdered cut hCut leftColumn) =
      (Frame.ofMountain mountain).rawParent (frontierAt hValid.toOrdered cut hCut rightColumn) := by
  classical
  let T := Frame.ofMountain mountain
  let rowAt := fun offset => (left[pair.leftBand.start + offset]?.getD phantom).row
  let eligible := (Finset.range (pair.gap.length + 1)).filter fun offset => rowAt offset ≤ cut
  have hNonempty : eligible.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    change (left[pair.leftBand.start + 0]?.getD phantom).row ≤ cut
    simpa only [Nat.add_zero, pair.leftBand.low_row] using hLow
  let offset := eligible.max' hNonempty
  have hChosen := Finset.mem_filter.mp (Finset.max'_mem eligible hNonempty)
  have hOffsetLe : offset ≤ pair.gap.length := by
    have h := Finset.mem_range.mp hChosen.1
    omega
  have hOffset : offset < pair.gap.length := by
    by_contra hn
    have he : offset = pair.gap.length := by omega
    have hh := hChosen.2
    change (left[pair.leftBand.start + offset]?.getD phantom).row ≤ cut at hh
    rw [he, pair.leftBand.high_row] at hh
    exact (not_le_of_gt hHigh) hh
  have hAbove : cut < rowAt (offset + 1) := by
    by_contra hn
    have hm : offset + 1 ∈ eligible := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), le_of_not_gt hn⟩
    have hi : offset + 1 ≤ offset := Finset.le_max' eligible _ hm
    omega
  have hLRead := pair.leftBand.offset_read hLeft hOffsetLe
  have hRRead := pair.rightBand.offset_read hRight hOffsetLe
  have hLURead := pair.leftBand.offset_read hLeft (show offset + 1 ≤ pair.gap.length by omega)
  have hRURead := pair.rightBand.offset_read hRight (show offset + 1 ≤ pair.gap.length by omega)
  obtain ⟨ln, hLNRef, hLNCell⟩ := Canonical.frame_node_of_cellAt hLRead
  obtain ⟨rn, hRNRef, hRNCell⟩ := Canonical.frame_node_of_cellAt hRRead
  obtain ⟨lu, hLURef, hLUCell⟩ := Canonical.frame_node_of_cellAt hLURead
  obtain ⟨ru, hRURef, hRUCell⟩ := Canonical.frame_node_of_cellAt hRURead
  have hLUpper : T.upper ln = some lu := Frame.upper_of_refs hLNRef (by simpa only [Nat.add_assoc] using hLURef)
  have hRUpper : T.upper rn = some ru := Frame.upper_of_refs hRNRef (by simpa only [Nat.add_assoc] using hRURef)
  have hLColumn : ln.1 = leftColumn := Fin.ext (congrArg Ref.column hLNRef)
  have hRColumn : rn.1 = rightColumn := Fin.ext (congrArg Ref.column hRNRef)
  have hLBelow : T.height ln ≤ cut := by
    change (T.cell ln).row ≤ cut
    rw [hLNCell]
    exact hChosen.2
  have hRBelow : T.height rn ≤ cut := by
    change (T.cell rn).row ≤ cut
    rw [hRNCell, ← pair.rows_agree hOffsetLe]
    exact hChosen.2
  have hLUAbove : cut < T.height lu := by
    change cut < (T.cell lu).row
    rw [hLUCell]
    exact hAbove
  have hRUAbove : cut < T.height ru := by
    change cut < (T.cell ru).row
    rw [hRUCell, ← pair.rows_agree (show offset + 1 ≤ pair.gap.length by omega)]
    exact hAbove
  have hLF : frontierAt hValid.toOrdered cut hCut leftColumn = ln := by
    rw [← hLColumn]
    apply frontierAt_eq_of_upper_barrier hValid.toOrdered hCut hLBelow
    intro upper hUpper
    exact Option.some.inj (hLUpper.symm.trans hUpper) ▸ hLUAbove
  have hRF : frontierAt hValid.toOrdered cut hCut rightColumn = rn := by
    rw [← hRColumn]
    apply frontierAt_eq_of_upper_barrier hValid.toOrdered hCut hRBelow
    intro upper hUpper
    exact Option.some.inj (hRUpper.symm.trans hUpper) ▸ hRUAbove
  have hParents : (T.cell lu).left = (T.cell ru).left := by
    rw [hLUCell, hRUCell]
    simpa only [Nat.add_assoc] using pair.leftBand.parentsAgree pair.rightBand offset hOffset
  rw [hLF, hRF]
  change T.rawParent ln = T.rawParent rn
  unfold Frame.rawParent
  rw [hLUpper, hRUpper]
  change ((T.cell lu).left >>= T.lookup) = ((T.cell ru).left >>= T.lookup)
  rw [hParents]

/-- The raw forest depths agree at every actual inserted event, including
events contributed by unrelated columns, as long as its cut is in the
same half-open band interval. This is stronger than endpoint comparison. -/
theorem CommonMarkerBandPair.event_depth_eq
    {mountain : Mountain} (hValid : MountainValid mountain)
    {left right : Column} {low high : Row} (pair : CommonMarkerBandPair left right low high)
    (leftColumn rightColumn : Fin (Frame.ofMountain mountain).width)
    (hLeft : mountain[leftColumn.val]? = some left)
    (hRight : mountain[rightColumn.val]? = some right)
    (hWidth : 0 < mountain.size) {bound event : Nat} (hBound : bound < mountain.size)
    (hLeftBound : leftColumn.val ≤ bound) (hRightBound : rightColumn.val ≤ bound)
    (hLow : low ≤ (Frame.ofMountain mountain).eventCut event)
    (hHigh : (Frame.ofMountain mountain).eventCut event < high) :
    parentDepth (eventParentMap hValid.toOrdered hWidth bound event) leftColumn.val =
      parentDepth (eventParentMap hValid.toOrdered hWidth bound event) rightColumn.val := by
  have hParents := pair.frontierAt_rawParent_eq hValid leftColumn rightColumn hLeft hRight
    ((Frame.ofMountain mountain).eventCut_one_le event) hLow hHigh
  let parents := eventParentMap hValid.toOrdered hWidth bound event
  have hMaps : parents leftColumn.val = parents rightColumn.val := by
    dsimp only [parents]
    rw [eventParentMap_raw_at hValid.toOrdered hWidth event leftColumn hLeftBound,
      eventParentMap_raw_at hValid.toOrdered hWidth event rightColumn hRightBound]
    exact congrArg (Option.map fun node => node.1.val) hParents
  have hLeftward : Leftward parents := eventParentMap_leftward hValid.toOrdered hWidth hBound event
  change parentDepth parents leftColumn.val = parentDepth parents rightColumn.val
  cases hm : parents leftColumn.val with
  | none => rw [parentDepth_none hm, parentDepth_none (hMaps.symm.trans hm)]
  | some father => rw [parentDepth_some hLeftward hm, parentDepth_some hLeftward (hMaps.symm.trans hm)]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.MarkerBand.offset_read
#print axioms OmegaY.Expansion.CommonMarkerBandPair.rows_agree
#print axioms OmegaY.Expansion.CommonMarkerBandPair.frontierAt_rawParent_eq
#print axioms OmegaY.Expansion.CommonMarkerBandPair.event_depth_eq
