/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RemainingMarkerParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMarkerParentEdge
import OmegaY.Expansion.RemainingActiveGeometry

/-!
# Closing stationary residuals with a strict-right root-row parent

Actual contour/seam provenance transfers stationarity to the source
parent's own root interval. Its exact root-row condition then forces the
target to remain at that root row. The already copied physical marker
supplies the executable parent selection and its raw output geometry.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Both remaining actual origins close when their numerical source
father is a strict-right physical marker at an actual root-interval row.
There is no positive-degree, raised-target or child-interval premise. -/
theorem DynamicBlockState.remaining_marker_parent_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    (hSource : p.reduced[next]? = some d.sources)
    {column : Column} {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row)
    {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    (hCone : Frame.RootCone (Frame.ofMountain p.reduced) a.root parent)
    (hParentRow : (Frame.ofMountain p.reduced).height parent = rootRow)
    (hRight : p.root.column < parent.1.val)
    (hLowerRead : column[index]? = some lower)
    (hUpperRead : column[index + 1]? = some upper) :
    CopiedRawAt ambient column lower upper := by
  have hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump rootRow a.degree) parent := by
    refine ⟨hCone, ?_, ?_⟩
    · rw [hParentRow, a.root_row]
    · rw [hParentRow]
      exact Row.lt_bump _ _
  obtain ⟨sourceUpper, originalUpper, hSourceUpper, hChildFixed, _, hActual, hShape⟩ :=
    origin.active_source_execution hSource hParent hChildColumn hChildRow a hInside
  obtain ⟨copied, parentRef, parentCell, hExpected, _, _, hLeft, _, hBefore,
      hRead, _, hBound, hB⟩ := s.copyEdge_stationary_marker_parent a hParent hCone hParentRow
    hChildColumn hRight hSourceUpper hChildFixed
  have he : copied = originalUpper := Except.ok.inj (hExpected.symm.trans hActual)
  have hOutputLeft : upper.left = some parentRef := hShape.2.symm.trans (he ▸ hLeft)
  have hOutputB : upper.row = Row.B lower.row parentCell.row := by
    rw [← hChildRow]
    exact hShape.1.symm.trans (he ▸ hB)
  have hReturned : ReturnedContourEdge ambient column index lower upper :=
    ⟨parentRef, parentCell,
      cellAt_ok_iff.mpr ⟨column, by simp, hLowerRead⟩,
      cellAt_ok_iff.mpr ⟨column, by simp, hUpperRead⟩,
      hOutputLeft, hBefore, (cellAt_push_left hBefore).trans hRead,
      hChildRow ▸ hBound, hOutputB⟩
  exact hReturned.raw_geometry

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.remaining_marker_parent_geometry
