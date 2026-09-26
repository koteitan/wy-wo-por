/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RaisedSeamGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.SeamSourceAt

/-! Raised lower endpoints at joins between actual marker segments. The
upper physical marker is fixed by the preceding segment's lift, because
the actual reference cap lies at or below that next marker. -/

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

theorem ExecutedSegmentSeam.upper_fixed_by_lower_lift
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {index : Nat} {lower upper : Cell} (seam : ExecutedSegmentSeam d index lower upper) :
    Row.lift (d.marker_data seam.lowMarker seam.low_member).current.row
      (d.marker_data seam.lowMarker seam.low_member).targetCell.row
      (d.marker_data seam.highMarker seam.high_member).current.row =
        (d.marker_data seam.highMarker seam.high_member).current.row := by
  obtain ⟨degree, hTarget, hHigh⟩ := d.reference_caps seam.lowMarker seam.low_member
    seam.highMarker seam.high_member seam.marker_order
  exact Row.lift_eq_of_ge_cap (d.marker_data seam.lowMarker seam.low_member).target_lower hTarget hHigh

section ActualSeam

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (d : ColumnCopyData ambient p.marked references next
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
  {column : Column} {index : Nat} {lower upper : Cell}
  (seam : ExecutedSegmentSeam d index lower upper)
  (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
    ColumnPowerSteps (d.marker_data marker hm).parentNodes)
  (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
    (d.marker_data marker hm).parentNodes[i]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row)
  (hNoPremature : NoPrematureOne d.sources)
  (hRun : copyColumn ambient p.marked references next
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
  (hLowerRead : column[index]? = some lower)
  (hUpperRead : column[index + 1]? = some upper)

include s history hLast hParentPower hParentLow hRun hLowerRead hUpperRead

theorem DynamicBlockState.raised_seam_source_geometry {sourceLower : Cell}
    (hSourceLower : d.sources[seam.highMarker.index - 1]? = some sourceLower)
    (hLowerRow : lower.row = Row.lift (d.marker_data seam.lowMarker seam.low_member).current.row
      (d.marker_data seam.lowMarker seam.low_member).targetCell.row sourceLower.row)
    (hRaisedLower : sourceLower.row < lower.row) :
    ReturnedContourEdge ambient column index lower upper := by
  let md := d.marker_data seam.lowMarker seam.low_member
  let hd := d.marker_data seam.highMarker seam.high_member
  have hSpec := p.marker_iff.mp (show BucketMem p.marked next ⟨next, 0⟩ from d.phantom_marker)
  obtain ⟨phantom, phantomNodes, hPhantomColumn, _⟩ := hSpec.2.2.1
  have hNext : next < p.reduced.size := (Array.getElem?_eq_some_iff.mp hPhantomColumn).1
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hSourceRead : Canonical.cellAt p.reduced ⟨next, seam.highMarker.index - 1⟩ = .ok sourceLower :=
    cellAt_ok_iff.mpr ⟨d.sources, hSource, hSourceLower⟩
  have hUpperReadSource : Canonical.cellAt p.reduced ⟨next, seam.highMarker.index⟩ = .ok hd.current :=
    cellAt_ok_iff.mpr ⟨d.sources, hSource, hd.current_at⟩
  obtain ⟨child, hChildRef, hChildCell⟩ := Canonical.frame_node_of_cellAt hSourceRead
  obtain ⟨sourceUpper, hSourceUpperRef, hSourceUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperReadSource
  have hChildColumn : child.1.val = next := congrArg Ref.column hChildRef
  have hChildIndex : child.2.val = seam.highMarker.index - 1 := congrArg Ref.index hChildRef
  have hAfter : seam.lowMarker.index ≤ child.2.val := by have := seam.marker_order; omega
  have hUpper : (Frame.ofMountain p.reduced).upper child = some sourceUpper :=
    upper_of_actual_refs hChildRef (by
      simpa only [show seam.highMarker.index - 1 + 1 = seam.highMarker.index by
        have := seam.marker_order; omega] using hSourceUpperRef)
  have hChildRaised : (Frame.ofMountain p.reduced).height child < lower.row := by
    simpa only [Frame.height, hChildCell] using hRaisedLower
  have hLowerLift : lower.row = Row.lift md.current.row md.targetCell.row
      ((Frame.ofMountain p.reduced).height child) := by
    simpa only [Frame.height, hChildCell] using hLowerRow
  rcases s.marker_source_transport hLast d seam.low_member hChildColumn hAfter with
    ⟨_, hFixed⟩ | ⟨rootIndex, a, hTarget, hRaised, hInterval | ⟨_, hFixed⟩⟩
  · exact False.elim ((ne_of_lt hChildRaised) (hLowerLift.trans hFixed).symm)
  · have hNormal := build_normal_of_success p.reduced_build
    have hPositive : 0 < (Frame.ofMountain p.reduced).height child :=
      Row.zero_lt_one.trans_le ((Frame.one_le_height hNormal.toOrdered a.root_real).trans hInterval.2.1)
    have hReal : Frame.Real child := by
      by_contra hn
      have hi : child.2.val = 0 := by unfold Frame.Real at hn; omega
      have hFin : child.2 = ⟨0, by have := child.2.isLt; omega⟩ := Fin.ext hi
      have hZero : (Frame.ofMountain p.reduced).height child = 0 := by
        change ((Frame.ofMountain p.reduced).cells child.1 child.2).row = 0
        rw [hFin, hNormal.phantom]
        rfl
      rw [hZero] at hPositive
      exact (lt_irrefl _) hPositive
    obtain ⟨parent, hParent, _⟩ := hNormal.upper_step child sourceUpper hReal hUpper
    have hCopy : copyEdge ambient (Frame.ref sourceUpper)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift md.current.row a.target.row ((Frame.ofMountain p.reduced).height sourceUpper)) =
          .ok seam.originalUpper := by
      rw [hSourceUpperRef]
      change copyEdge ambient ⟨next, seam.highMarker.index⟩ _ _
        (Row.lift md.current.row a.target.row ((Frame.ofMountain p.reduced).cell sourceUpper).row) = _
      rw [hSourceUpperCell, hTarget, seam.upper_fixed_by_lower_lift]
      exact (seam.upper_copy hParentPower hParentLow).1
    have hLowerTarget : lower.row = Row.lift md.current.row a.target.row
        ((Frame.ofMountain p.reduced).height child) := by simpa only [hTarget] using hLowerLift
    obtain ⟨parentRef, actualParent, hLow, hHigh, hLeft, _, hRead, hParentRow, hB⟩ :=
      s.returned_interval_edge history hLast a hRaised hInterval hParent hChildColumn hUpper
        hLowerRead hUpperRead hCopy seam.upper_shape hLowerTarget
    have hParentBound : actualParent.row ≤ lower.row := by
      rw [hParentRow, hLowerTarget]
      exact a.interval_parent_row_le hRaised hInterval hParent
    obtain ⟨actualColumn, hActualRun, _, hValid, _, _⟩ := d.copyColumn_valid
    have hSame : actualColumn = column := Except.ok.inj (hActualRun.symm.trans hRun)
    subst actualColumn
    exact ⟨parentRef, actualParent, hLow, hHigh, hLeft,
      (hValid.stored_valid _ _ _ hUpperRead hLeft).1, hRead, hParentBound, hB⟩
  · exact False.elim ((ne_of_lt hChildRaised) (hLowerLift.trans hFixed).symm)

include hNoPremature

theorem DynamicBlockState.raised_seam_geometry :
    ∃ sourceLower, d.sources[seam.highMarker.index - 1]? = some sourceLower ∧
      lower.row = Row.lift (d.marker_data seam.lowMarker seam.low_member).current.row
        (d.marker_data seam.lowMarker seam.low_member).targetCell.row sourceLower.row ∧
      (sourceLower.row < lower.row → ReturnedContourEdge ambient column index lower upper) := by
  obtain ⟨sourceLower, hRead, _, hLowerRow, _⟩ := seam.source_predecessor hParentPower hParentLow hNoPremature
  exact ⟨sourceLower, hRead, hLowerRow, s.raised_seam_source_geometry history hLast d seam
    hParentPower hParentLow hRun hLowerRead hUpperRead hRead hLowerRow⟩

end ActualSeam

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedSegmentSeam.upper_fixed_by_lower_lift
#print axioms OmegaY.Expansion.DynamicBlockState.raised_seam_source_geometry
#print axioms OmegaY.Expansion.DynamicBlockState.raised_seam_geometry
