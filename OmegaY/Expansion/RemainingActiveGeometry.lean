/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RemainingActiveGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRemainingRaw
import OmegaY.Expansion.InheritedMarkers

/-!
# Remaining stationary edges with an active source father

The source father's active interval need not be the interval queried by
the child's last marker. Actual marker inheritance and the absence of
intervening markers make both source endpoints stationary for that other
interval too. The existing active-parent selector then determines the
real copied edge. Source P and root intervals here concern the frozen
build; output numerical first-smaller recovery is not assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A stationary source pair can use any active father's actual reference
interval. The successful original-row copy is matched by determinism,
and its shape is transferred to the caller's actual output reads. -/
theorem DynamicBlockState.returned_active_source_copy_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references sourceIndex rootRow)
    {child parent sourceUpper : (Frame.ofMountain p.reduced).Node}
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root (Row.bump rootRow a.degree) parent)
    (hAbove : rootRow < (Frame.ofMountain p.reduced).height parent)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hSourceUpper : (Frame.ofMountain p.reduced).upper child = some sourceUpper)
    (hChildFixed : Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child) =
      (Frame.ofMountain p.reduced).height child)
    (hUpperFixed : Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height sourceUpper) =
      (Frame.ofMountain p.reduced).height sourceUpper)
    {originalUpper : Cell}
    (hActual : copyEdge ambient (Frame.ref sourceUpper)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      ((Frame.ofMountain p.reduced).height sourceUpper) = .ok originalUpper)
    {column : Column} {index : Nat} {lower upper : Cell}
    (hLowerRow : lower.row = (Frame.ofMountain p.reduced).height child)
    (hUpperShape : SameShape originalUpper upper)
    (hLowerRead : column[index]? = some lower)
    (hUpperRead : column[index + 1]? = some upper) :
    ReturnedContourEdge ambient column index lower upper := by
  obtain ⟨copied, parentRef, parentCell, hExpected, _, hLeft, _, hRead, _, hBound, hB⟩ :=
    s.copyEdge_active_parent history hLast a hInside hAbove hParent hChildColumn hSourceUpper
  rw [hUpperFixed] at hExpected
  rw [hChildFixed] at hBound hB
  have he : copied = originalUpper := Except.ok.inj (hExpected.symm.trans hActual)
  have hOutputLeft : upper.left = some parentRef := hUpperShape.2.symm.trans (he ▸ hLeft)
  have hOutputB : upper.row = Row.B lower.row parentCell.row := by
    rw [hLowerRow]
    exact hUpperShape.1.symm.trans (he ▸ hB)
  obtain ⟨parentColumn, hParentColumn, _⟩ := cellAt_ok_iff.mp hRead
  have hBefore : parentRef.column < ambient.size := (Array.getElem?_eq_some_iff.mp hParentColumn).1
  exact ⟨parentRef, parentCell,
    cellAt_ok_iff.mpr ⟨column, by simp, hLowerRead⟩,
    cellAt_ok_iff.mpr ⟨column, by simp, hUpperRead⟩,
    hOutputLeft, hBefore, (cellAt_push_left hBefore).trans hRead,
    hLowerRow ▸ hBound, hOutputB⟩

/-- Both exact residual constructors discharge their marker and
stationarity obligations internally. The external source child is
identified with their stored source node by actual column/row uniqueness.
The active father may be controlled by a different, lower marker. -/
theorem RemainingMovedStationaryOrigin.active_source_execution
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    {d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column}
    {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper)
    (hSource : p.reduced[next]? = some d.sources)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row)
    {sourceIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references sourceIndex rootRow)
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root (Row.bump rootRow a.degree) parent) :
    ∃ (sourceUpper : (Frame.ofMountain p.reduced).Node) (originalUpper : Cell),
      (Frame.ofMountain p.reduced).upper child = some sourceUpper ∧
      Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child) =
        (Frame.ofMountain p.reduced).height child ∧
      Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height sourceUpper) =
        (Frame.ofMountain p.reduced).height sourceUpper ∧
      copyEdge ambient (Frame.ref sourceUpper)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        ((Frame.ofMountain p.reduced).height sourceUpper) = .ok originalUpper ∧
      SameShape originalUpper upper := by
  have hOrdered := p.reduced_valid.toOrdered
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  have hRight : p.root.column < next := by
    have hp := Frame.P_column_lt hOrdered hParent
    have hr := Frame.RootCone.column_le hOrdered hInside.1
    rw [hRootColumn] at hr
    rw [hChildColumn] at hp
    exact hr.trans_lt hp
  cases origin with
  | contour_inside pair pathIndex _ _ _ execution source hStationary _ _ hCopy =>
    have hSourceColumn : source.lowerNode.1.val = next := congrArg Ref.column source.lower_ref
    have hSourceRow : (Frame.ofMountain p.reduced).height source.lowerNode = lower.row := by
      simpa only [Frame.height, source.lower_cell] using hStationary
    have hChildEq : source.lowerNode = child := Frame.node_eq_of_column_height hOrdered
      (Fin.ext (hSourceColumn.trans hChildColumn.symm)) (hSourceRow.trans hChildRow.symm)
    have hSourceParent : (Frame.ofMountain p.reduced).P source.lowerNode = some parent := by
      rw [hChildEq]
      exact hParent
    have hSourceIndex : source.lowerNode.2.val = pair.marker.index + pathIndex + 1 :=
      congrArg Ref.index source.lower_ref
    have hAfter : pair.marker.index ≤ source.lowerNode.2.val := by omega
    have hNoBetween : ∀ middle, pair.marker.index < middle → middle ≤ source.lowerNode.2.val →
        middle ∉ d.bucket.map Ref.index := by
      intro middle hlo hhi
      exact execution.no_markers middle hlo (by omega)
    have hOwnStationary : Row.lift (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row
        ((Frame.ofMountain p.reduced).height source.lowerNode) =
          (Frame.ofMountain p.reduced).height source.lowerNode := by
      simpa only [Frame.height, source.lower_cell] using
        execution.lower_row.symm.trans (pair.lower_shape.1.trans hStationary.symm)
    obtain ⟨hChildFixed, hUpperFixed⟩ := d.stationary_child_for_active_parent hSource a pair.member
      hSourceParent hInside hSourceColumn hRight hAfter hNoBetween source.source_upper hOwnStationary
    have hActual : copyEdge ambient (Frame.ref source.upperNode)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        ((Frame.ofMountain p.reduced).height source.upperNode) = .ok pair.originalUpper := by
      simpa only [Frame.height, source.upper_cell] using hCopy
    exact ⟨source.upperNode, pair.originalUpper,
      by simpa only [hChildEq] using source.source_upper,
      by simpa only [hChildEq] using hChildFixed,
      hUpperFixed, hActual, pair.upper_shape⟩
  | cross_segment seam sourceLower _ hLowerLift source hStationary _ _ hCopy =>
    have hSourceColumn : source.lowerNode.1.val = next := congrArg Ref.column source.lower_ref
    have hSourceRow : (Frame.ofMountain p.reduced).height source.lowerNode = lower.row := by
      simpa only [Frame.height, source.lower_cell] using hStationary
    have hChildEq : source.lowerNode = child := Frame.node_eq_of_column_height hOrdered
      (Fin.ext (hSourceColumn.trans hChildColumn.symm)) (hSourceRow.trans hChildRow.symm)
    have hSourceParent : (Frame.ofMountain p.reduced).P source.lowerNode = some parent := by
      rw [hChildEq]
      exact hParent
    have hSourceIndex : source.lowerNode.2.val = seam.highMarker.index - 1 :=
      congrArg Ref.index source.lower_ref
    have hAfter : seam.lowMarker.index ≤ source.lowerNode.2.val := by have := seam.marker_order; omega
    have hNoBetween : ∀ middle, seam.lowMarker.index < middle → middle ≤ source.lowerNode.2.val →
        middle ∉ d.bucket.map Ref.index := by
      intro middle hlo hhi hMem
      obtain ⟨marker, hm, he⟩ := List.mem_map.mp hMem
      apply seam.no_between marker hm
      have := seam.marker_order
      exact ⟨by omega, by omega⟩
    have hOwnStationary : Row.lift (d.marker_data seam.lowMarker seam.low_member).current.row
        (d.marker_data seam.lowMarker seam.low_member).targetCell.row
        ((Frame.ofMountain p.reduced).height source.lowerNode) =
          (Frame.ofMountain p.reduced).height source.lowerNode := by
      simpa only [Frame.height, source.lower_cell] using hLowerLift.symm.trans hStationary.symm
    obtain ⟨hChildFixed, hUpperFixed⟩ := d.stationary_child_for_active_parent hSource a seam.low_member
      hSourceParent hInside hSourceColumn hRight hAfter hNoBetween source.source_upper hOwnStationary
    have hActual : copyEdge ambient (Frame.ref source.upperNode)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        ((Frame.ofMountain p.reduced).height source.upperNode) = .ok seam.originalUpper := by
      simpa only [Frame.height, source.upper_cell] using hCopy
    exact ⟨source.upperNode, seam.originalUpper,
      by simpa only [hChildEq] using source.source_upper,
      by simpa only [hChildEq] using hChildFixed,
      hUpperFixed, hActual, seam.upper_shape⟩

/-- Every remaining edge with a strictly-above-root active source father
has the required raw geometry, for any actual parent-root interval. -/
theorem DynamicBlockState.remaining_active_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    (hSource : p.reduced[next]? = some d.sources)
    {column : Column} {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row)
    {sourceIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references sourceIndex rootRow)
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root (Row.bump rootRow a.degree) parent)
    (hAbove : rootRow < (Frame.ofMountain p.reduced).height parent)
    (hLowerRead : column[index]? = some lower)
    (hUpperRead : column[index + 1]? = some upper) :
    CopiedRawAt ambient column lower upper := by
  obtain ⟨sourceUpper, originalUpper, hSourceUpper, hChildFixed, hUpperFixed, hActual, hShape⟩ :=
    origin.active_source_execution hSource hParent hChildColumn hChildRow a hInside
  exact (s.returned_active_source_copy_geometry history hLast a hInside hAbove hParent
    hChildColumn hSourceUpper hChildFixed hUpperFixed hActual hChildRow.symm
    hShape hLowerRead hUpperRead).raw_geometry

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.returned_active_source_copy_geometry
#print axioms OmegaY.Expansion.RemainingMovedStationaryOrigin.active_source_execution
#print axioms OmegaY.Expansion.DynamicBlockState.remaining_active_geometry
