/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/MarkerBandParentColumn.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CommonMarkerBandEvents
import OmegaY.Expansion.ActualMarkedFrontierCopy

/-!
# The actual parent column throughout a marker fill band

The finite band determines its actual frontier and upper offset at every
interior cut. All fill cells retain the same parent column, though their
parent indices change. This gives the raw event-parent column without
assuming a numerical-parent identification or a target frontier.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem fillCellsAscending_left_column {nodes : Column} {column : Nat} {low high : Row} {cell : Cell}
    (hMem : cell ∈ fillCellsAscending nodes column low high) :
    ∃ index, cell.left = some ⟨column, index⟩ := by
  obtain ⟨index, _, hCell⟩ := List.mem_flatMap.mp hMem
  have hChunk := List.mem_reverse.mp hCell
  unfold fillChunk at hChunk
  dsimp only at hChunk
  split at hChunk
  · obtain ⟨row, _, rfl⟩ := List.mem_map.mp hChunk
    exact ⟨index, rfl⟩
  · simp at hChunk

theorem MarkerBand.event_parent_column
    {mountain : Mountain} (hValid : MountainValid mountain)
    {nodes : Column} {gap : List Cell} {low high : Row}
    (band : MarkerBand nodes gap low high)
    (column : Fin (Frame.ofMountain mountain).width)
    (hColumn : mountain[column.val]? = some nodes)
    {parentColumn : Nat} (hParents : ∀ cell ∈ gap, ∃ index, cell.left = some ⟨parentColumn, index⟩)
    (hWidth : 0 < mountain.size) {bound event : Nat} (hBound : column.val ≤ bound)
    (hLow : low ≤ (Frame.ofMountain mountain).eventCut event)
    (hHigh : (Frame.ofMountain mountain).eventCut event < high) :
    eventParentMap hValid.toOrdered hWidth bound event column.val = some parentColumn := by
  classical
  let F := Frame.ofMountain mountain
  let cut := F.eventCut event
  let rowAt := fun offset => (nodes[band.start + offset]?.getD phantom).row
  let eligible := (Finset.range (gap.length + 1)).filter fun offset => rowAt offset ≤ cut
  have hNonempty : eligible.Nonempty := by
    refine ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩⟩
    change (nodes[band.start + 0]?.getD phantom).row ≤ cut
    simpa only [Nat.add_zero, band.low_row] using hLow
  let offset := eligible.max' hNonempty
  have hChosen := Finset.mem_filter.mp (Finset.max'_mem eligible hNonempty)
  have hOffsetLe : offset ≤ gap.length := by
    have h := Finset.mem_range.mp hChosen.1
    omega
  have hOffset : offset < gap.length := by
    by_contra hn
    have he : offset = gap.length := by omega
    have hh := hChosen.2
    change (nodes[band.start + offset]?.getD phantom).row ≤ cut at hh
    rw [he, band.high_row] at hh
    exact (not_le_of_gt hHigh) hh
  have hAbove : cut < rowAt (offset + 1) := by
    by_contra hn
    have hm : offset + 1 ∈ eligible := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), le_of_not_gt hn⟩
    have hi : offset + 1 ≤ offset := Finset.le_max' eligible _ hm
    omega
  obtain ⟨node, hNodeRef, hNodeCell⟩ := Canonical.frame_node_of_cellAt (band.offset_read hColumn hOffsetLe)
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt
    (band.offset_read hColumn (show offset + 1 ≤ gap.length by omega))
  have hUpper : F.upper node = some upper := Frame.upper_of_refs hNodeRef
    (by simpa only [Nat.add_assoc] using hUpperRef)
  have hNodeColumn : node.1 = column := Fin.ext (congrArg Ref.column hNodeRef)
  have hBelow : F.height node ≤ cut := by
    change (F.cell node).row ≤ cut
    rw [hNodeCell]
    exact hChosen.2
  have hUpperAbove : cut < F.height upper := by
    change cut < (F.cell upper).row
    rw [hUpperCell]
    exact hAbove
  have hFront : eventFrontier hValid.toOrdered event column = node := by
    rw [← hNodeColumn]
    apply frontierAt_eq_of_upper_barrier hValid.toOrdered (F.eventCut_one_le event) hBelow
    intro other hOther
    exact Option.some.inj (hUpper.symm.trans hOther) ▸ hUpperAbove
  obtain ⟨parentIndex, hParent⟩ := hParents gap[offset] (List.getElem_mem hOffset)
  have hStored : (F.cell upper).left = some ⟨parentColumn, parentIndex⟩ := by
    rw [hUpperCell]
    exact (band.upper_shape offset hOffset).2.symm.trans hParent
  obtain ⟨parent, hLookup, _, _⟩ := hValid.toOrdered.stored_valid upper _ hStored
  have hParentColumn : parent.1.val = parentColumn := congrArg Ref.column (lookup_spec hLookup)
  have hRaw : F.rawParent node = some parent := by
    unfold Frame.rawParent
    rw [hUpper]
    change (F.cell upper).left >>= F.lookup = some parent
    rw [hStored]
    exact hLookup
  rw [eventParentMap_raw_at hValid.toOrdered hWidth event column hBound, hFront, hRaw]
  exact congrArg some hParentColumn

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- Real marker execution fixes the numerical source parent's shifted
column as the raw event parent at every physical/effective interior cut.
The source parent may itself lie in the root column. -/
theorem marker_band_event_parent_column
    (hLast : 1 < last) (hValid : MountainValid result) (hWidth : 0 < result.size)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    {event : Nat} (hLow : (Frame.ofMountain p.reduced).height source ≤ (Frame.ofMountain result).eventCut event)
    (hHigh : (Frame.ofMountain result).eventCut event < copy.read.outputCell.row) :
    eventParentMap hValid.toOrdered hWidth (result.size - 1) event copy.outputRef.column =
      some (parent.1.val + block * (p.reduced.size - 1 - p.root.column)) := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  let md := d.marker_data (Frame.ref source) hMarked
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := real_of_value_pos hNormal.toOrdered
    ((P_value hNormal.toOrdered hParent).1.trans (P_value hNormal.toOrdered hParent).2)
  have hPositive := Row.zero_lt_one.trans_le (one_le_height hNormal.toOrdered hReal)
  have hSources : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient _ source.1.isLt).symm.trans d.source_column
  have hCurrent : md.current = F.cell source := Option.some.inj (md.current_at.symm.trans copy.read.source_at)
  obtain ⟨sourceUpper, hSourceUpper⟩ := hNormal.upper_of_parent hParent
  have hUpperAt : d.sources[source.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSources (congrArg Fin.val (upper_spec hSourceUpper).1)
    simpa only [(upper_spec hSourceUpper).2] using hRead
  have hUpperCell : md.upper = F.cell sourceUpper := Option.some.inj (md.upper_at.symm.trans hUpperAt)
  obtain ⟨actualParent, hActual, _, _, hStored⟩ := hNormal.upper_step source sourceUpper hReal hSourceUpper
  have he : actualParent = parent := Option.some.inj (hActual.symm.trans hParent)
  subst actualParent
  have hSourceParent : md.sourceParent = Frame.ref parent := Option.some.inj
    (md.upper_left.symm.trans (by simpa only [hUpperCell] using hStored))
  obtain ⟨hNoPremature, hPP, hPL⟩ := copy.state.column_data_parent_inputs hLast source.1.isLt d
  obtain ⟨band⟩ := d.copyColumn_marker_band hPP hPL hNoPremature copy.read.copy_run hMarked
    (by change 0 < md.current.row; rw [hCurrent]; exact hPositive)
  have hResult : result[copy.before.size]? = some copy.column := copy.preserved.column_read (by simp)
  have hColumnBound := (Array.getElem?_eq_some_iff.mp hResult).1
  let column : Fin (Frame.ofMountain result).width := ⟨copy.before.size, hColumnBound⟩
  have hTarget : md.targetCell.row = copy.read.outputCell.row := Except.ok.inj
    (md.reference.symm.trans (by simpa only [hCurrent] using copy.read.marked_reference hMarked))
  have hMap := band.event_parent_column hValid column hResult
    (fun _ h => fillCellsAscending_left_column h) hWidth
      (show column.val ≤ result.size - 1 by dsimp only [column]; omega)
      (by change md.current.row ≤ _; rw [hCurrent]; exact hLow) (hHigh.trans_eq hTarget.symm)
  change eventParentMap hValid.toOrdered hWidth (result.size - 1) event copy.before.size =
    some (md.sourceParent.column + _) at hMap
  change eventParentMap hValid.toOrdered hWidth (result.size - 1) event copy.before.size = _
  simpa only [hSourceParent, Frame.ref] using hMap

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.fillCellsAscending_left_column
#print axioms OmegaY.Expansion.MarkerBand.event_parent_column
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.marker_band_event_parent_column
