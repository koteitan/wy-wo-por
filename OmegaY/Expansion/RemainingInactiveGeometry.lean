/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RemainingInactiveGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.DynamicInactiveParent
import OmegaY.Expansion.RemainingMarkerParent

/-!
# Inactive-parent geometry for actual remaining edges

The real residual origin supplies the source upper's executed copy and
its returned shape. Only the controlling marker's local cap test is needed
to apply the history-based parent selector. No output numerical P or
separate copy success is supplied by the caller.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Recover the actual unchanged-row copy call from either remaining
origin, identifying its source child by column and row. -/
theorem RemainingMovedStationaryOrigin.source_execution
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {ambient : Mountain} {references : List Ref} {next : Nat}
    {d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column}
    {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper)
    {child : (Frame.ofMountain p.reduced).Node}
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row) :
    ∃ (sourceUpper : (Frame.ofMountain p.reduced).Node) (originalUpper : Cell),
      (Frame.ofMountain p.reduced).upper child = some sourceUpper ∧
      copyEdge ambient (Frame.ref sourceUpper)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        ((Frame.ofMountain p.reduced).height sourceUpper) = .ok originalUpper ∧
      SameShape originalUpper upper := by
  have hOrdered := p.reduced_valid.toOrdered
  cases origin with
  | contour_inside pair pathIndex _ _ _ execution source hStationary _ _ hCopy =>
    have hSourceColumn : source.lowerNode.1.val = next := congrArg Ref.column source.lower_ref
    have hSourceRow : (Frame.ofMountain p.reduced).height source.lowerNode = lower.row := by
      simpa only [Frame.height, source.lower_cell] using hStationary
    have he : source.lowerNode = child := Frame.node_eq_of_column_height hOrdered
      (Fin.ext (hSourceColumn.trans hChildColumn.symm)) (hSourceRow.trans hChildRow.symm)
    exact ⟨source.upperNode, pair.originalUpper,
      by simpa only [he] using source.source_upper,
      by simpa only [Frame.height, source.upper_cell] using hCopy, pair.upper_shape⟩
  | cross_segment seam sourceLower _ _ source hStationary _ _ hCopy =>
    have hSourceColumn : source.lowerNode.1.val = next := congrArg Ref.column source.lower_ref
    have hSourceRow : (Frame.ofMountain p.reduced).height source.lowerNode = lower.row := by
      simpa only [Frame.height, source.lower_cell] using hStationary
    have he : source.lowerNode = child := Frame.node_eq_of_column_height hOrdered
      (Fin.ext (hSourceColumn.trans hChildColumn.symm)) (hSourceRow.trans hChildRow.symm)
    exact ⟨source.upperNode, seam.originalUpper,
      by simpa only [he] using source.source_upper,
      by simpa only [Frame.height, source.upper_cell] using hCopy, seam.upper_shape⟩

/-- Close both residual origins when the actual controlling reference cap
lies at or below the source father. The local copy call is recovered from
the origin and the earlier parent-column run from history. -/
theorem DynamicBlockState.remaining_inactive_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    {column : Column} {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row)
    (hRight : p.root.column < parent.1.val)
    {marker : Ref} (hm : marker ∈ p.marked[parent.1.val]?.getD []) {markerCell : Cell}
    (hMarkerRead : Canonical.cellAt p.reduced marker = .ok markerCell)
    (hIndex : marker.index ≤ parent.2.val)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ parent.2.val →
      middle ∉ (p.marked[parent.1.val]?.getD []).map Ref.index)
    {target : Row} (hReference : referenceAt start references markerCell.row = .ok target)
    {degree : Nat} (hTargetCap : target < Row.bump markerCell.row degree)
    (hCap : Row.bump markerCell.row degree ≤ (Frame.ofMountain p.reduced).height parent)
    (hLowerRead : column[index]? = some lower)
    (hUpperRead : column[index + 1]? = some upper) :
    CopiedRawAt ambient column lower upper := by
  obtain ⟨sourceUpper, originalUpper, hSourceUpper, hActual, hShape⟩ :=
    origin.source_execution hChildColumn hChildRow
  obtain ⟨copied, parentRef, parentCell, hExpected, _, _, hLeft, _, hRead, hRow, hB⟩ :=
    s.copyEdge_inactive_parent history hLast hParent hChildColumn hSourceUpper hRight
      hm hMarkerRead hIndex hNoBetween hReference hTargetCap hCap
  have he : copied = originalUpper := Except.ok.inj (hExpected.symm.trans hActual)
  have hOutputLeft : upper.left = some parentRef := hShape.2.symm.trans (he ▸ hLeft)
  have hOutputB : upper.row = Row.B lower.row parentCell.row := by
    rw [← hChildRow]
    exact hShape.1.symm.trans (he ▸ hB)
  obtain ⟨parentColumn, hParentColumn, _⟩ := cellAt_ok_iff.mp hRead
  have hBefore : parentRef.column < ambient.size := (Array.getElem?_eq_some_iff.mp hParentColumn).1
  have hBound : parentCell.row ≤ lower.row := by
    rw [hRow, ← hChildRow]
    exact Frame.P_height_le p.reduced_valid.toOrdered hParent
  have hReturned : ReturnedContourEdge ambient column index lower upper :=
    ⟨parentRef, parentCell,
      cellAt_ok_iff.mpr ⟨column, by simp, hLowerRead⟩,
      cellAt_ok_iff.mpr ⟨column, by simp, hUpperRead⟩,
      hOutputLeft, hBefore, (cellAt_push_left hBefore).trans hRead, hBound, hOutputB⟩
  exact hReturned.raw_geometry

/-- Above an unraised controlling marker, the successor cap suffices.
The marker-height equality case is intentionally not hidden in this lemma. -/
theorem DynamicBlockState.remaining_unraised_above_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    {column : Column} {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row)
    (hRight : p.root.column < parent.1.val)
    {marker : Ref} (hm : marker ∈ p.marked[parent.1.val]?.getD []) {markerCell : Cell}
    (hMarkerRead : Canonical.cellAt p.reduced marker = .ok markerCell)
    (hIndex : marker.index ≤ parent.2.val)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ parent.2.val →
      middle ∉ (p.marked[parent.1.val]?.getD []).map Ref.index)
    (hReference : referenceAt start references markerCell.row = .ok markerCell.row)
    (hAbove : markerCell.row < (Frame.ofMountain p.reduced).height parent)
    (hLowerRead : column[index]? = some lower)
    (hUpperRead : column[index + 1]? = some upper) :
    CopiedRawAt ambient column lower upper := by
  have hCap : Row.bump markerCell.row 0 ≤ (Frame.ofMountain p.reduced).height parent := by
    by_contra hn
    have hj := Row.jump_le_of_lt_bump hAbove.le (lt_of_not_ge hn)
    have he := Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero hj)
    exact (ne_of_lt hAbove) he
  exact s.remaining_inactive_geometry history hLast d origin hParent hChildColumn hChildRow
    hRight hm hMarkerRead hIndex hNoBetween hReference (Row.lt_bump _ 0) hCap hLowerRead hUpperRead

end OmegaY.Expansion

#print axioms OmegaY.Expansion.RemainingMovedStationaryOrigin.source_execution
#print axioms OmegaY.Expansion.DynamicBlockState.remaining_inactive_geometry
#print axioms OmegaY.Expansion.DynamicBlockState.remaining_unraised_above_geometry
