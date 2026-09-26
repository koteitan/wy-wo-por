/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/StationarySeamGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RaisedSeamGeometry
import OmegaY.Expansion.StationaryContourGeometry

/-!
# Stored geometry at stationary segment joins

The actual seam supplies the physical upper marker and its source
predecessor. A nonzero stationary lower output excludes a phantom source
predecessor. Source Normal then supplies its P father. Fixed-column fathers
give the full stored geometry without any source P premise; the separate
active-parent interface retains its explicit source interval condition.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem upper_of_actual_refs {F : Frame} {before after : F.Node} {column index : Nat}
    (hBefore : Frame.ref before = ⟨column, index⟩)
    (hAfter : Frame.ref after = ⟨column, index + 1⟩) : F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hBefore hAfter
  have hc : d = c := Fin.ext (hAfter.1.trans hBefore.1.symm)
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, by omega⟩

section ActualSeam

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
  (s : DynamicBlockState p block start references next ambient)
  (d : ColumnCopyData ambient p.marked references next
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
  {column : Column} {index : Nat} {lower upper : Cell}
  (seam : ExecutedSegmentSeam d index lower upper)

include s in
private theorem stationary_source_pair {sourceLower : Cell}
    (hSourceLower : d.sources[seam.highMarker.index - 1]? = some sourceLower)
    (hStationary : sourceLower.row = lower.row) (hNonzero : lower.row ≠ 0) :
    ∃ child sourceUpper : (Frame.ofMountain p.reduced).Node,
      Frame.ref child = ⟨next, seam.highMarker.index - 1⟩ ∧
      Frame.ref sourceUpper = ⟨next, seam.highMarker.index⟩ ∧
      (Frame.ofMountain p.reduced).cell child = sourceLower ∧
      (Frame.ofMountain p.reduced).cell sourceUpper =
        (d.marker_data seam.highMarker seam.high_member).current ∧
      Frame.Real child ∧ (Frame.ofMountain p.reduced).upper child = some sourceUpper := by
  let hd := d.marker_data seam.highMarker seam.high_member
  have hSpec := p.marker_iff.mp (show BucketMem p.marked next ⟨next, 0⟩ from d.phantom_marker)
  obtain ⟨_, phantomNodes, hPhantomColumn, _⟩ := hSpec.2.2.1
  have hNext : next < p.reduced.size := (Array.getElem?_eq_some_iff.mp hPhantomColumn).1
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hRead : Canonical.cellAt p.reduced ⟨next, seam.highMarker.index - 1⟩ = .ok sourceLower :=
    cellAt_ok_iff.mpr ⟨d.sources, hSource, hSourceLower⟩
  have hUpperRead : Canonical.cellAt p.reduced ⟨next, seam.highMarker.index⟩ = .ok hd.current :=
    cellAt_ok_iff.mpr ⟨d.sources, hSource, hd.current_at⟩
  obtain ⟨child, hChildRef, hChildCell⟩ := Canonical.frame_node_of_cellAt hRead
  obtain ⟨sourceUpper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hReal : Frame.Real child := by
    by_contra hn
    have hi : child.2.val = 0 := by unfold Frame.Real at hn; omega
    have hFin : child.2 = ⟨0, by have := child.2.isLt; omega⟩ := Fin.ext hi
    have hZero : (Frame.ofMountain p.reduced).height child = 0 := by
      change ((Frame.ofMountain p.reduced).cells child.1 child.2).row = 0
      rw [hFin, p.reduced_valid.toOrdered.phantom]
      rfl
    have hOutputZero : lower.row = 0 := by
      rw [← hStationary]
      simpa only [Frame.height, hChildCell] using hZero
    exact hNonzero hOutputZero
  exact ⟨child, sourceUpper, hChildRef, hUpperRef, hChildCell, hUpperCell, hReal,
    upper_of_actual_refs hChildRef (by
      simpa only [show seam.highMarker.index - 1 + 1 = seam.highMarker.index by
        have := seam.marker_order; omega] using hUpperRef)⟩

variable
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[i]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hRun : copyColumn ambient p.marked references next
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
  (hLowerRead : column[index]? = some lower)
  (hUpperRead : column[index + 1]? = some upper)

include hRun hLowerRead hUpperRead in
private theorem returned_from_seam_copy {requested : Row} {source : Ref}
    {candidate : Cell} {parentRef : Ref} {parentCell : Cell}
    (hExpected : copyEdge ambient source (block * (p.reduced.size - 1 - p.root.column))
      p.root.column requested = .ok candidate)
    (hActual : copyEdge ambient source (block * (p.reduced.size - 1 - p.root.column))
      p.root.column requested = .ok seam.originalUpper)
    (hLeft : candidate.left = some parentRef)
    (hRead : Canonical.cellAt ambient parentRef = .ok parentCell)
    (hBound : parentCell.row ≤ lower.row) (hB : candidate.row = Row.B lower.row parentCell.row) :
    ReturnedContourEdge ambient column index lower upper := by
  have he : candidate = seam.originalUpper := Except.ok.inj (hExpected.symm.trans hActual)
  have hOutputLeft : upper.left = some parentRef := seam.upper_shape.2.symm.trans (he ▸ hLeft)
  obtain ⟨actualColumn, hActualRun, _, hValid, _, _⟩ := d.copyColumn_valid
  have hSame : actualColumn = column := Except.ok.inj (hActualRun.symm.trans hRun)
  subst actualColumn
  have hLeftward := (hValid.stored_valid _ _ _ hUpperRead hOutputLeft).1
  exact ⟨parentRef, parentCell,
    cellAt_ok_iff.mpr ⟨column, by simp, hLowerRead⟩,
    cellAt_ok_iff.mpr ⟨column, by simp, hUpperRead⟩,
    hOutputLeft, hLeftward, (cellAt_push_left hLeftward).trans hRead,
    hBound, seam.upper_shape.1.symm.trans (he ▸ hB)⟩

include s hParentPower hParentLow hRun hLowerRead hUpperRead

/-- The fixed-column stationary seam case. The old source father is
identified from the actual physical upper marker's stored endpoint. -/
theorem DynamicBlockState.stationary_seam_source_geometry {sourceLower : Cell}
    (hSourceLower : d.sources[seam.highMarker.index - 1]? = some sourceLower)
    (hLowerRow : lower.row = Row.lift (d.marker_data seam.lowMarker seam.low_member).current.row
      (d.marker_data seam.lowMarker seam.low_member).targetCell.row sourceLower.row)
    (hStationary : sourceLower.row = lower.row) (hNonzero : lower.row ≠ 0)
    {oldParentRef : Ref}
    (hOldLeft : (d.marker_data seam.highMarker seam.high_member).current.left = some oldParentRef)
    (hFixed : oldParentRef.column < p.root.column) :
    ReturnedContourEdge ambient column index lower upper := by
  let md := d.marker_data seam.lowMarker seam.low_member
  obtain ⟨child, sourceUpper, hChildRef, hUpperRef, hChildCell, hUpperCell, hReal, hSourceUpper⟩ :=
    stationary_source_pair s d seam hSourceLower hStationary hNonzero
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨parent, hParent, _, _, hStored⟩ := hNormal.upper_step child sourceUpper hReal hSourceUpper
  have hStored' : (d.marker_data seam.highMarker seam.high_member).current.left =
      some (Frame.ref parent) := by simpa only [hUpperCell] using hStored
  have hParentRef : Frame.ref parent = oldParentRef := Option.some.inj (hStored'.symm.trans hOldLeft)
  have hRootLow : md.current.row ≤ (Frame.ofMountain p.reduced).height child := by
    have hLow := d.marker_source_row_le seam.low_member hSourceLower
      (by have := seam.marker_order; omega)
    simpa only [Frame.height, hChildCell] using hLow
  have hLowerSource : lower.row = (Frame.ofMountain p.reduced).height child := by
    simpa only [Frame.height, hChildCell] using hStationary.symm
  have hLiftFixed : Row.lift md.current.row md.targetCell.row ((Frame.ofMountain p.reduced).height child) =
      (Frame.ofMountain p.reduced).height child := by
    simpa only [Frame.height, hChildCell] using hLowerRow.symm.trans hStationary.symm
  obtain ⟨hExpected, hRead, hBound, hB⟩ := s.copyEdge_stationary_fixed_parent hRootLow hLiftFixed
    hParent hSourceUpper
    (by change (Frame.ref parent).column < p.root.column; rw [hParentRef]; exact hFixed)
  rw [hLiftFixed] at hBound hB
  have hActual : copyEdge ambient (Frame.ref sourceUpper)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift md.current.row md.targetCell.row ((Frame.ofMountain p.reduced).height sourceUpper)) =
      .ok seam.originalUpper := by
    rw [hUpperRef]
    change copyEdge ambient ⟨next, seam.highMarker.index⟩ _ _
      (Row.lift md.current.row md.targetCell.row ((Frame.ofMountain p.reduced).cell sourceUpper).row) = _
    rw [hUpperCell, seam.upper_fixed_by_lower_lift]
    exact (seam.upper_copy hParentPower hParentLow).1
  exact returned_from_seam_copy d seam hRun hLowerRead hUpperRead hExpected hActual rfl hRead
    (by simpa only [hLowerSource, Frame.height] using hBound)
    (by simpa only [hLowerSource, Frame.height] using hB)

/-- The source predecessor and common lift come from the actual seam
execution, including the empty-contour/fill-endpoint case. -/
theorem DynamicBlockState.stationary_seam_geometry
    (hNoPremature : NoPrematureOne d.sources) (hNonzero : lower.row ≠ 0)
    {oldParentRef : Ref}
    (hOldLeft : (d.marker_data seam.highMarker seam.high_member).current.left = some oldParentRef)
    (hFixed : oldParentRef.column < p.root.column) :
    ∃ sourceLower, d.sources[seam.highMarker.index - 1]? = some sourceLower ∧
      lower.row = Row.lift (d.marker_data seam.lowMarker seam.low_member).current.row
        (d.marker_data seam.lowMarker seam.low_member).targetCell.row sourceLower.row ∧
      (sourceLower.row = lower.row → ReturnedContourEdge ambient column index lower upper) := by
  obtain ⟨sourceLower, hRead, _, hLowerRow, _⟩ := seam.source_predecessor hParentPower hParentLow hNoPremature
  exact ⟨sourceLower, hRead, hLowerRow, fun hStationary =>
    s.stationary_seam_source_geometry d seam hParentPower hParentLow hRun hLowerRead hUpperRead
      hRead hLowerRow hStationary hNonzero hOldLeft hFixed⟩

/-- A stationary seam with a strictly interior active source father. The
source RootInterval condition remains explicit. Both the source P father
and the successful moved copy are derived, and the returned parent may be
higher than its original source row. -/
theorem DynamicBlockState.active_stationary_seam_source_geometry
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceLower : Cell}
    (hSourceLower : d.sources[seam.highMarker.index - 1]? = some sourceLower)
    (hLowerRow : lower.row = Row.lift (d.marker_data seam.lowMarker seam.low_member).current.row
      (d.marker_data seam.lowMarker seam.low_member).targetCell.row sourceLower.row)
    (hStationary : sourceLower.row = lower.row) (hNonzero : lower.row ≠ 0)
    {sourceIndex : Nat}
    (a : ActualRootInterval p start ambient references sourceIndex
      (d.marker_data seam.lowMarker seam.low_member).current.row)
    (hTarget : a.target.row = (d.marker_data seam.lowMarker seam.low_member).targetCell.row)
    {sourceParent : (Frame.ofMountain p.reduced).Node}
    (hStored : (d.marker_data seam.highMarker seam.high_member).current.left = some (Frame.ref sourceParent))
    (hParentInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump (d.marker_data seam.lowMarker seam.low_member).current.row a.degree) sourceParent)
    (hParentAbove : (d.marker_data seam.lowMarker seam.low_member).current.row <
      (Frame.ofMountain p.reduced).height sourceParent) :
    ReturnedContourEdge ambient column index lower upper := by
  let md := d.marker_data seam.lowMarker seam.low_member
  obtain ⟨child, sourceUpper, hChildRef, hUpperRef, hChildCell, hUpperCell, hReal, hSourceUpper⟩ :=
    stationary_source_pair s d seam hSourceLower hStationary hNonzero
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨parent, hParent, _, _, hOldStored⟩ := hNormal.upper_step child sourceUpper hReal hSourceUpper
  have hStored' : (d.marker_data seam.highMarker seam.high_member).current.left =
      some (Frame.ref parent) := by simpa only [hUpperCell] using hOldStored
  have hParentRef : Frame.ref parent = Frame.ref sourceParent := Option.some.inj (hStored'.symm.trans hStored)
  have hParentEq : parent = sourceParent := Executable.ref_injective _ hParentRef
  subst parent
  have hChildColumn : child.1.val = next := congrArg Ref.column hChildRef
  obtain ⟨candidate, parentRef, parentCell, hExpected, _, hLeft, _, hRead, _, hBound, hB⟩ :=
    s.copyEdge_active_parent history hLast a hParentInside hParentAbove hParent hChildColumn hSourceUpper
  have hActual : copyEdge ambient (Frame.ref sourceUpper)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift md.current.row a.target.row ((Frame.ofMountain p.reduced).height sourceUpper)) =
      .ok seam.originalUpper := by
    rw [hUpperRef]
    change copyEdge ambient ⟨next, seam.highMarker.index⟩ _ _
      (Row.lift md.current.row a.target.row ((Frame.ofMountain p.reduced).cell sourceUpper).row) = _
    rw [hUpperCell, hTarget, seam.upper_fixed_by_lower_lift]
    exact (seam.upper_copy hParentPower hParentLow).1
  have hLowerLift : lower.row = Row.lift md.current.row a.target.row
      ((Frame.ofMountain p.reduced).height child) := by
    simpa only [Frame.height, hChildCell, hTarget] using hLowerRow
  exact returned_from_seam_copy d seam hRun hLowerRead hUpperRead hExpected hActual hLeft hRead
    (by simpa only [hLowerLift] using hBound) (by simpa only [hLowerLift] using hB)

end ActualSeam

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.stationary_seam_source_geometry
#print axioms OmegaY.Expansion.DynamicBlockState.stationary_seam_geometry
#print axioms OmegaY.Expansion.DynamicBlockState.active_stationary_seam_source_geometry
