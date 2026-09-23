/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkerParentBounds.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualStationaryMarkerUpper

/-!
# A real marker's parent never lies strictly left of the root column

The executed marker enumeration gives a same-row parent path to a real
root-column node. Its first edge forces the parent's column bound and
row equality, including the case where that parent is itself in the root
column. This removes a needless strict-right restriction from the actual
stationary-marker upper-row theorem.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem build_marked_parent_bounds {input : List Nat} {mountain : Mountain}
    (hBuild : build input = .ok mountain)
    {root child parent : (Frame.ofMountain mountain).Node} {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref root) = .ok marked)
    (hParent : (Frame.ofMountain mountain).P child = some parent)
    (hMarked : BucketMem marked (Frame.ref child).column (Frame.ref child)) :
    root.1.val ≤ parent.1.val ∧
      (Frame.ofMountain mountain).height child = (Frame.ofMountain mountain).height parent := by
  have hNormal := build_normal_of_success hBuild
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨hChildRight, low, _, hColumn, _, hPath, hRow⟩ :=
    (build_markers_real_member_iff_parentPath hBuild hMarkers hReal).mp hMarked
  cases hPath with
  | refl =>
      have he := congrArg Fin.val hColumn
      omega
  | @cons child next low hNext tail =>
      have he : next = parent := Option.some.inj (hNext.symm.trans hParent)
      subst next
      have hBound : root.1.val ≤ parent.1.val := by
        simpa only [hColumn] using tail.column_le hNormal.toOrdered
      have hSame : (Frame.ofMountain mountain).height parent =
          (Frame.ofMountain mountain).height child := le_antisymm
        (Frame.P_height_le hNormal.toOrdered hParent)
        (by rw [hRow]; exact tail.height_le hNormal.toOrdered)
      exact ⟨hBound, hSame.symm⟩

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

theorem stationary_marker_upper_read_all (hLast : 1 < last)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent sourceUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hStationary : copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source)
    (hSourceUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper) :
    ∃ upperCell, Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok upperCell ∧
      upperCell.row = (Frame.ofMountain p.reduced).height sourceUpper := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  let md := d.marker_data (Frame.ref source) hMarked
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hSources : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hCurrent : md.current = F.cell source := Option.some.inj (md.current_at.symm.trans copy.read.source_at)
  have hUpperAt : d.sources[source.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSources (congrArg Fin.val (Frame.upper_spec hSourceUpper).1)
    simpa only [(Frame.upper_spec hSourceUpper).2] using hRead
  have hUpperCell : md.upper = F.cell sourceUpper := Option.some.inj (md.upper_at.symm.trans hUpperAt)
  obtain ⟨actualParent, hActualParent, hB, _, hStored⟩ := hNormal.upper_step source sourceUpper hReal hSourceUpper
  have he : actualParent = parent := Option.some.inj (hActualParent.symm.trans hParent)
  subst actualParent
  have hSourceParent : md.sourceParent = Frame.ref parent := Option.some.inj
    (md.upper_left.symm.trans (by simpa only [hUpperCell] using hStored))
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨hParentBound, hSame⟩ := build_marked_parent_bounds p.reduced_build hMarkers hParent hMarked
  change F.height source = F.height parent at hSame
  have hSourceUpperRow : md.upper.row = Row.bump md.current.row 0 := by
    rw [hUpperCell, hCurrent]
    change F.height sourceUpper = Row.bump (F.height source) 0
    change F.height sourceUpper = Row.B (F.height source) (F.height parent) at hB
    simpa only [← hSame, Row.B_self] using hB
  have hRoot : p.root.column ≤ md.sourceParent.column := by
    rw [hSourceParent]
    exact (congrArg Ref.column hRootRef).symm.trans_le hParentBound
  have hPhysicalRow : copy.read.outputCell.row = md.current.row :=
    hStationary.trans (congrArg Cell.row hCurrent).symm
  obtain ⟨hNoPremature, hPP, hPL⟩ := copy.state.column_data_parent_inputs hLast source.1.isLt d
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hPL (Frame.ref source) hMarked
  obtain ⟨upper, hUpperRead, hUpperRow, _⟩ := d.physical_marker_upper
    hPP hPL hNoPremature copy.read.copy_run hMarked hSourceUpperRow hRoot hLow hLowRow
    copy.read.output_at hPhysicalRow
  refine ⟨upper, ?_, hUpperRow.trans (hSourceUpperRow.symm.trans (congrArg Cell.row hUpperCell))⟩
  exact (copy.preserved.cellAt
    (ref := ⟨copy.outputRef.column, copy.outputRef.index + 1⟩)
    (by simp [outputRef, EffectiveCopyRead.outputRef])).trans
    (cellAt_ok_iff.mpr ⟨copy.column, by simp [outputRef, EffectiveCopyRead.outputRef], hUpperRead⟩)

/-- Every stationary marker preserves its actual upper height, with no
restriction to the unchanged high tail. -/
theorem upper_height_of_stationary_marker_all (hLast : 1 < last)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent sourceUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hStationary : copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source)
    (hSourceUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper)
    {target targetUpper : (Frame.ofMountain result).Node}
    (hTargetRef : Frame.ref target = copy.outputRef)
    (hTargetUpper : (Frame.ofMountain result).upper target = some targetUpper) :
    (Frame.ofMountain result).height targetUpper = (Frame.ofMountain p.reduced).height sourceUpper := by
  obtain ⟨upperCell, hRead, hRow⟩ := copy.stationary_marker_upper_read_all
    hLast hMarked hParent hStationary hSourceUpper
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hRead
  have he : upper = targetUpper := Option.some.inj
    ((Frame.upper_of_refs hTargetRef hUpperRef).symm.trans hTargetUpper)
  rw [← he, Frame.height, hUpperCell]
  exact hRow

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_marked_parent_bounds
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.stationary_marker_upper_read_all
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.upper_height_of_stationary_marker_all
