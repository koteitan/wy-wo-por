/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkerCone.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootInterval
import OmegaY.Expansion.PreparedParentInterval

/-!
# Actual markers identify the root cone of a reference interval

The marker bucket was built by the executable weak-path search. Source
normality translates that search into an actual same-row parent path. Row
uniqueness in the root column identifies its endpoint with the root stored
in the actual reference certificate.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem positive_height_real {F : Frame} (hF : F.Ordered) {u : F.Node}
    (hHeight : 0 < F.height u) : Frame.Real u := by
  by_contra hn
  have hi : u.2.val = 0 := by unfold Frame.Real at hn; omega
  have hi' : u.2 = ⟨0, by have := u.2.isLt; omega⟩ := Fin.ext hi
  change 0 < (F.cells u.1 u.2).row at hHeight
  rw [hi', hF.phantom] at hHeight
  exact (lt_irrefl (0 : Row)) hHeight

theorem ActualRootInterval.rootCone_of_marker
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    {marker : (Frame.ofMountain p.reduced).Node}
    (hMarker : BucketMem p.marked marker.1.val (Frame.ref marker))
    (hRow : (Frame.ofMountain p.reduced).height marker = sourceRow) :
    Frame.RootCone (Frame.ofMountain p.reduced) a.root marker := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hPositive : 0 < sourceRow := by
    rw [← a.root_row]
    exact Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered a.root_real)
  have hReal : Frame.Real marker := positive_height_real hNormal.toOrdered (hRow ▸ hPositive)
  obtain ⟨badRoot, hBadRef, _⟩ := frame_node_of_cellAt (cellAt_ok_iff.mp p.restored_root)
  have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
    simpa only [hBadRef] using p.markers_built
  obtain ⟨_, low, hLowReal, hLowColumn, _, hPath, hLowRow⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hReal).mp hMarker
  have hColumn : low.1 = a.root.1 := Fin.ext
    ((congrArg Fin.val hLowColumn).trans
      ((congrArg Ref.column hBadRef).trans (congrArg Ref.column a.root_ref).symm))
  have hHeight : F.height low = F.height a.root :=
    hLowRow.symm.trans (hRow.trans a.root_row.symm)
  have hSame : low = a.root := Frame.node_eq_of_column_height hNormal.toOrdered hColumn hHeight
  exact ⟨marker, hReal, rfl, hRow.trans a.root_row.symm, hSame ▸ hPath⟩

/-- A source node in the marker's column and row interval belongs to the
actual certificate's cone. No independently selected ancestor path is an
input. -/
theorem ActualRootInterval.inside_of_marker
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    {marker node : (Frame.ofMountain p.reduced).Node}
    (hMarker : BucketMem p.marked marker.1.val (Frame.ref marker))
    (hRow : (Frame.ofMountain p.reduced).height marker = sourceRow)
    (hColumn : marker.1 = node.1)
    (hLower : sourceRow ≤ (Frame.ofMountain p.reduced).height node)
    (hUpper : (Frame.ofMountain p.reduced).height node < Row.bump sourceRow a.degree) :
    Frame.RootInterval (Frame.ofMountain p.reduced) a.root (Row.bump sourceRow a.degree) node :=
  ⟨(a.rootCone_of_marker hMarker hRow).same_column hColumn,
    a.root_row.trans_le hLower, hUpper⟩

/-- The actual copy data and marker index supply the source lower bound.
Only the upper-interval test remains as a case condition. -/
theorem ColumnCopyData.actual_marker_source_interval
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {index sourceColumn shift : Nat}
    {sourceRow : Row}
    (d : ColumnCopyData ambient p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (a : ActualRootInterval p start ambient references index sourceRow)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hMarkerRow : (d.marker_data marker hm).current.row = sourceRow)
    {node : (Frame.ofMountain p.reduced).Node} (hColumn : node.1.val = sourceColumn)
    (hAfter : marker.index ≤ node.2.val)
    (hBelow : (Frame.ofMountain p.reduced).height node < Row.bump sourceRow a.degree) :
    Frame.RootInterval (Frame.ofMountain p.reduced) a.root (Row.bump sourceRow a.degree) node := by
  let md := d.marker_data marker hm
  have hMarkerRead : Canonical.cellAt p.reduced marker = .ok md.current :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns marker hm] using hSource, md.current_at⟩
  obtain ⟨actualMarker, hMarkerRef, hMarkerCell⟩ := frame_node_of_cellAt (cellAt_ok_iff.mp hMarkerRead)
  have hActualColumn : actualMarker.1.val = sourceColumn :=
    (congrArg Ref.column hMarkerRef).trans (d.marker_columns marker hm)
  have hMember : BucketMem p.marked actualMarker.1.val (Frame.ref actualMarker) := by
    rw [hActualColumn, hMarkerRef]
    exact hm
  have hRow : (Frame.ofMountain p.reduced).height actualMarker = sourceRow := by
    change ((Frame.ofMountain p.reduced).cell actualMarker).row = sourceRow
    rw [hMarkerCell]
    exact hMarkerRow
  have hNodeRead := d.frame_source_read hSource hColumn
  have hLow : sourceRow ≤ (Frame.ofMountain p.reduced).height node := by
    rcases eq_or_lt_of_le hAfter with he | hl
    · have hSame : md.current = (Frame.ofMountain p.reduced).cell node :=
        Option.some.inj (md.current_at.symm.trans (by simpa only [he] using hNodeRead))
      exact hMarkerRow.symm.trans_le (le_of_eq (congrArg Cell.row hSame))
    · have h := (d.source_valid.rows_strict _ _ _ _ md.current_at hNodeRead hl).le
      simpa only [md, hMarkerRow, Frame.height] using h
  exact a.inside_of_marker hMember hRow (Fin.ext (hActualColumn.trans hColumn.symm)) hLow hBelow

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualRootInterval.rootCone_of_marker
#print axioms OmegaY.Expansion.ActualRootInterval.inside_of_marker
#print axioms OmegaY.Expansion.ColumnCopyData.actual_marker_source_interval
