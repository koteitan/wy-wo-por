/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InheritedMarkers.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.InheritedRootCone
import OmegaY.Expansion.ActualMarkerTransport

/-! A real parent-root marker is inherited in its child's source column.
The child's own last marker can be higher. Thus active-parent copying must
not silently identify the two controlling roots. -/

namespace OmegaY.Expansion

open Canonical Geometry

theorem ActualRootInterval.child_marker_witness
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root (Row.bump rootRow a.degree) parent)
    (hRight : p.root.column < child.1.val) :
    ∃ low : (Frame.ofMountain p.reduced).Node, Frame.Real low ∧ low.1 = child.1 ∧
      (Frame.ofMountain p.reduced).height low = rootRow ∧ low.2.val ≤ child.2.val ∧
      BucketMem p.marked child.1.val (Frame.ref low) := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨low, hReal, hColumn, hRow, _, hIndex, hPath⟩ :=
    hInside.1.child_witness hNormal hParent hInside.2.1
  obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
    simpa only [hBadRef] using p.markers_built
  have hRootColumn : a.root.1 = badRoot.1 := Fin.ext
    ((congrArg Ref.column a.root_ref).trans (congrArg Ref.column hBadRef).symm)
  have hMember := (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hReal).mpr
    ⟨by simpa only [hColumn, show badRoot.1.val = p.root.column from congrArg Ref.column hBadRef] using hRight,
      a.root, a.root_real, hRootColumn,
      by simpa only [show a.root.2.val = rootIndex from congrArg Ref.index a.root_ref,
        show badRoot.2.val = p.root.index from congrArg Ref.index hBadRef] using a.root_prefix,
      hPath, hRow⟩
  exact ⟨low, hReal, hColumn, hRow.trans a.root_row, hIndex,
    by simpa only [Frame.ref, hColumn] using hMember⟩

/-- For an actual maximal source marker, the inherited parent-root row
cannot lie above its current row. The parent may be in a different cone. -/
theorem ColumnCopyData.active_parent_root_le_marker
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {rootIndex sourceColumn shift : Nat} {rootRow : Row}
    (d : ColumnCopyData ambient p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {marker : Ref} (hm : marker ∈ d.bucket)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root (Row.bump rootRow a.degree) parent)
    (hChildColumn : child.1.val = sourceColumn) (hRight : p.root.column < sourceColumn)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ child.2.val →
      middle ∉ d.bucket.map Ref.index) :
    rootRow ≤ (d.marker_data marker hm).current.row := by
  obtain ⟨low, _, hColumn, hRow, hIndex, hMember⟩ := a.child_marker_witness hParent hInside
    (by simpa only [hChildColumn] using hRight)
  have hLowMember : Frame.ref low ∈ d.bucket := by
    change BucketMem p.marked sourceColumn (Frame.ref low)
    simpa only [hChildColumn] using hMember
  have hLowIndex : low.2.val ≤ marker.index := by
    by_contra hn
    exact hNoBetween low.2.val (Nat.lt_of_not_ge hn) hIndex
      (List.mem_map.mpr ⟨Frame.ref low, hLowMember, rfl⟩)
  have hLowRead := d.frame_source_read hSource
    (show low.1.val = sourceColumn by rw [hColumn, hChildColumn])
  have hCurrent : (d.marker_data (Frame.ref low) hLowMember).current = (Frame.ofMountain p.reduced).cell low :=
    Option.some.inj ((d.marker_data (Frame.ref low) hLowMember).current_at.symm.trans hLowRead)
  have hBound := d.marker_source_row_le hLowMember (d.marker_data marker hm).current_at hLowIndex
  simpa only [hCurrent, ← hRow, Frame.height] using hBound

/-- A higher actual marker lies at or above this root's real upper
barrier. This uses marker enumeration, so it also covers sparse rows. -/
theorem ActualRootInterval.marker_ge_cap
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {rootIndex sourceColumn shift : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    (d : ColumnCopyData ambient p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hHigher : rootRow < (d.marker_data marker hm).current.row) :
    Row.bump rootRow a.degree ≤ (d.marker_data marker hm).current.row := by
  apply le_of_not_gt
  intro hBelow
  have hRead : Canonical.cellAt p.reduced marker = .ok (d.marker_data marker hm).current :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns marker hm] using hSource,
      (d.marker_data marker hm).current_at⟩
  exact marker_not_in_open_interval p.reduced_valid.toOrdered
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    ⟨p.rootCell, cellAt_ok_iff.mp p.restored_root⟩ p.markers_built
    (congrArg Ref.column a.root_ref) a.root_upper_barrier hm hRead
    ⟨by simpa only [a.root_row] using hHigher, hBelow⟩

/-- The parent's controlling root may differ from the child's marker.
If the actual child's own lift is stationary, its endpoints are also
stationary for every active source-parent interval. -/
theorem ColumnCopyData.stationary_child_for_active_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {rootIndex sourceColumn shift : Nat} {rootRow : Row}
    (d : ColumnCopyData ambient p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {marker : Ref} (hm : marker ∈ d.bucket)
    {child parent childUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root (Row.bump rootRow a.degree) parent)
    (hChildColumn : child.1.val = sourceColumn) (hRight : p.root.column < sourceColumn)
    (hAfter : marker.index ≤ child.2.val)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ child.2.val →
      middle ∉ d.bucket.map Ref.index)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hStationary : Row.lift (d.marker_data marker hm).current.row
      (d.marker_data marker hm).targetCell.row ((Frame.ofMountain p.reduced).height child) =
        (Frame.ofMountain p.reduced).height child) :
    Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child) =
        (Frame.ofMountain p.reduced).height child ∧
      Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height childUpper) =
        (Frame.ofMountain p.reduced).height childUpper := by
  let F := Frame.ofMountain p.reduced
  let md := d.marker_data marker hm
  have hNormal := build_normal_of_success p.reduced_build
  have hRootMarker := d.active_parent_root_le_marker hSource a hm hParent hInside hChildColumn hRight hNoBetween
  have hMarkerChild : md.current.row ≤ F.height child :=
    d.marker_source_row_le hm (d.frame_source_read hSource hChildColumn) hAfter
  have hLow : rootRow ≤ F.height child := hRootMarker.trans hMarkerChild
  have hChildFixed : Row.lift rootRow a.target.row (F.height child) = F.height child := by
    rcases eq_or_lt_of_le hRootMarker with hEqual | hStrict
    · have hEqual' : rootRow = md.current.row := hEqual
      have hTarget : a.target.row = md.targetCell.row := Except.ok.inj
        (a.ambient_query.symm.trans (by rw [hEqual']; exact md.reference))
      simpa only [hEqual', hTarget] using hStationary
    · exact Row.lift_eq_of_ge_cap a.target_lower a.target_below
        ((a.marker_ge_cap d hSource hm hStrict).trans hMarkerChild)
  have hUpperRow : F.height childUpper = Row.bump (F.height child)
      (Row.jump (F.height child) (F.height childUpper) - 1) := by
    obtain ⟨hColumn, hIndex⟩ := Frame.upper_spec hUpper
    have hLowRead := d.frame_source_read hSource hChildColumn
    have hHighRead := d.frame_source_read hSource
      (show childUpper.1.val = sourceColumn by rw [hColumn, hChildColumn])
    simpa only [hIndex, Frame.height] using d.source_power child.2.val (F.cell child) (F.cell childUpper)
      hLowRead (by simpa only [hIndex] using hHighRead)
  refine ⟨hChildFixed, ?_⟩
  conv_lhs => rw [hUpperRow]
  rw [Row.lift_bump hLow, hChildFixed, ← hUpperRow]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualRootInterval.child_marker_witness
#print axioms OmegaY.Expansion.ColumnCopyData.active_parent_root_le_marker
#print axioms OmegaY.Expansion.ActualRootInterval.marker_ge_cap
#print axioms OmegaY.Expansion.ColumnCopyData.stationary_child_for_active_parent
