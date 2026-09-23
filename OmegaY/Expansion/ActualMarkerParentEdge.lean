/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkerParentEdge.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.MarkerParentInterval
import OmegaY.Expansion.ActualRootInterval

/-!
# Stationary source parents at a strict-right physical root marker

The source father lies at the interval root's exact row and strictly to
the right of the bad-root column. Source Normal forces its child to the
same row and its child upper to the successor. Stationarity therefore
forces the actual reference target to equal that row. Actual copied-marker
support supplies the parent's real output read and strict-below selection.
No positive degree or child-interval hypothesis is needed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Same-row root-cone membership identifies the actual physical parent
as an enumerated marker. This works even when the interval degree is zero. -/
theorem ActualRootInterval.same_row_parent_marker
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hCone : Frame.RootCone (Frame.ofMountain p.reduced) a.root parent)
    (hRow : (Frame.ofMountain p.reduced).height parent = rootRow)
    (hRight : p.root.column < parent.1.val) :
    BucketMem p.marked parent.1.val (Frame.ref parent) := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref badRoot) = .ok p.marked := by
    simpa only [hBadRef] using p.markers_built
  have hBadColumn : badRoot.1.val = p.root.column := congrArg Ref.column hBadRef
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  obtain ⟨low, hLowColumn, hLowRow, hMember⟩ := rootCone_marker_witness hNormal
    (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
    hMarkers a.root_real (Fin.ext (hRootColumn.trans hBadColumn.symm))
    (by
      have hi : a.root.2.val = rootIndex := congrArg Ref.index a.root_ref
      have hb : badRoot.2.val = p.root.index := congrArg Ref.index hBadRef
      simpa only [hi, hb] using a.root_prefix)
    (by simpa only [hBadColumn] using hRight) hCone
  have he : low = parent := Frame.node_eq_of_column_height hNormal.toOrdered hLowColumn
    (hLowRow.trans (a.root_row.trans hRow.symm))
  have hRefEq : Frame.ref low = Frame.ref parent := congrArg Frame.ref he
  change BucketMem p.marked parent.1.val (Frame.ref low) at hMember
  rw [hRefEq] at hMember
  exact hMember

/-- At a strict-right physical root marker, source geometry plus a
stationary child forces the actual reference target to be unraised. -/
theorem ActualRootInterval.stationary_marker_parent_rows
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hCone : Frame.RootCone (Frame.ofMountain p.reduced) a.root parent)
    (hParentRow : (Frame.ofMountain p.reduced).height parent = rootRow)
    (hRight : p.root.column < parent.1.val)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hStationary : Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child) =
      (Frame.ofMountain p.reduced).height child) :
    (Frame.ofMountain p.reduced).height child = rootRow ∧
      (Frame.ofMountain p.reduced).height upper = Row.bump rootRow 0 ∧ a.target.row = rootRow := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  obtain ⟨hChild, hUpperRow⟩ := Frame.marker_parent_successor hNormal hParent hCone
    (hParentRow.trans a.root_row.symm) (by simpa only [hRootColumn] using hRight) hUpper
  have hChildRow : (Frame.ofMountain p.reduced).height child = rootRow := hChild.trans a.root_row
  have hUpperRow' : (Frame.ofMountain p.reduced).height upper = Row.bump rootRow 0 := by
    simpa only [a.root_row] using hUpperRow
  exact ⟨hChildRow, hUpperRow', by simpa only [hChildRow, Row.lift_at_root] using hStationary⟩

/-- The already copied physical parent marker supplies the exact real
selector below the unchanged source upper. Marker support is part of the
actual dynamic state and was established by the copying loop. -/
theorem DynamicBlockState.below_stationary_marker_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next rootIndex : Nat} {rootRow : Row}
    (s : DynamicBlockState p block start references next ambient)
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hCone : Frame.RootCone (Frame.ofMountain p.reduced) a.root parent)
    (hParentRow : (Frame.ofMountain p.reduced).height parent = rootRow)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hStationary : Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child) =
      (Frame.ofMountain p.reduced).height child) :
    ∃ (ref : Ref) (cell : Cell),
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        ((Frame.ofMountain p.reduced).height upper) = .ok ref ∧
      Canonical.cellAt ambient ref = .ok cell ∧
      ref.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      cell.row = (Frame.ofMountain p.reduced).height parent := by
  have hMember := a.same_row_parent_marker hCone hParentRow hRight
  obtain ⟨_, hUpperRow, hTarget⟩ := a.stationary_marker_parent_rows hParent hCone hParentRow hRight hUpper hStationary
  have hBefore : parent.1.val < next := by
    simpa only [hChildColumn] using Frame.P_column_lt p.reduced_valid.toOrdered hParent
  obtain ⟨column, hColumn, _, hRows⟩ := s.copied_columns parent.1.val hRight hBefore
  have hQuery : referenceAt start references ((Frame.ofMountain p.reduced).cell parent).row = .ok rootRow := by
    change referenceAt start references ((Frame.ofMountain p.reduced).height parent) = _
    rw [hParentRow]
    simpa only [hTarget] using a.start_query
  obtain ⟨index, cell, hRead, hRow⟩ :=
    (hRows (Frame.ref parent) hMember ((Frame.ofMountain p.reduced).cell parent)
      (cellAt_of_frame_node p.reduced parent) rootRow hQuery).2
  have hActual : Canonical.cellAt ambient
      ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), index⟩ = .ok cell :=
    cellAt_ok_iff.mpr ⟨column, hColumn, hRead⟩
  have hBelow := below_bump_zero_of_read s.ambient_valid hActual
  refine ⟨_, cell, ?_, hActual, rfl, hRow.trans hParentRow.symm⟩
  simpa only [hRow, hUpperRow] using hBelow

/-- Real copyEdge success, parent read and B geometry for the stationary
strict-right root-marker parent. All source stored-leg facts and the
destination bounds are derived from the canonical source and state. -/
theorem DynamicBlockState.copyEdge_stationary_marker_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next rootIndex : Nat} {rootRow : Row}
    (s : DynamicBlockState p block start references next ambient)
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hCone : Frame.RootCone (Frame.ofMountain p.reduced) a.root parent)
    (hParentRow : (Frame.ofMountain p.reduced).height parent = rootRow)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hStationary : Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child) =
      (Frame.ofMountain p.reduced).height child) :
    ∃ (copied : Cell) (actualRef : Ref) (actualParent : Cell),
      copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        ((Frame.ofMountain p.reduced).height upper) = .ok copied ∧
      copied.row = (Frame.ofMountain p.reduced).height upper ∧ copied.value = 0 ∧
      copied.left = some actualRef ∧
      actualRef.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      actualRef.column < ambient.size ∧ Canonical.cellAt ambient actualRef = .ok actualParent ∧
      actualParent.row = (Frame.ofMountain p.reduced).height parent ∧
      actualParent.row ≤ (Frame.ofMountain p.reduced).height child ∧
      copied.row = Row.B ((Frame.ofMountain p.reduced).height child) actualParent.row := by
  obtain ⟨actualRef, actualParent, hBelow, hRead, hColumn, hRow⟩ :=
    s.below_stationary_marker_parent a hParent hCone hParentRow hChildColumn hRight hUpper hStationary
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hChildReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldParent, hOldParent, hB, _, hStored⟩ := hNormal.upper_step child upper hChildReal hUpper
  have he : oldParent = parent := Option.some.inj (hOldParent.symm.trans hParent)
  subst oldParent
  have hSource : lookup ambient (Frame.ref upper) = .ok (F.cell upper) :=
    lookup_ok_iff.mpr (cellAt_ok_iff.mp
      (p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced upper)))
  change (F.cell upper).left = some (Frame.ref parent) at hStored
  have hNonzero : (F.cell upper).row ≠ 0 := by
    have hPositive := Frame.one_le_height hNormal.toOrdered (upper_real hUpper)
    intro hz
    change (1 : Row) ≤ (F.cell upper).row at hPositive
    rw [hz] at hPositive
    exact (not_le_of_gt Row.zero_lt_one) hPositive
  have hDestination : actualRef.column < (Frame.ref upper).column +
      block * (p.reduced.size - 1 - p.root.column) := by
    rw [hColumn]
    apply Nat.add_lt_add_right
    change parent.1.val < upper.1.val
    rw [(Frame.upper_spec hUpper).1]
    exact Frame.P_column_lt hNormal.toOrdered hParent
  have hUpperColumn : (Frame.ref upper).column = next :=
    (congrArg Fin.val (Frame.upper_spec hUpper).1).trans hChildColumn
  have hBefore : actualRef.column < ambient.size := by
    rw [s.size_eq, ← hUpperColumn]
    exact hDestination
  let copied : Cell := ⟨F.height upper, 0, some actualRef⟩
  refine ⟨copied, actualRef, actualParent, ?_, rfl, rfl, rfl, hColumn, hBefore, hRead,
    hRow, hRow ▸ Frame.P_height_le hNormal.toOrdered hParent, ?_⟩
  · have hMoved : ¬ (Frame.ref parent).column < p.root.column := Nat.not_lt_of_ge hRight.le
    change below ambient ((Frame.ref parent).column + block * (p.reduced.size - 1 - p.root.column))
      ((Frame.ofMountain p.reduced).height upper) = .ok actualRef at hBelow
    simp [copyEdge, copied, hSource, hNonzero, leftOf, hStored, hMoved, hBelow,
      Nat.not_le_of_gt hDestination]
    rfl
  · change F.height upper = Row.B (F.height child) actualParent.row
    rw [hRow]
    exact hB

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualRootInterval.same_row_parent_marker
#print axioms OmegaY.Expansion.ActualRootInterval.stationary_marker_parent_rows
#print axioms OmegaY.Expansion.DynamicBlockState.below_stationary_marker_parent
#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_stationary_marker_parent
