/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualStationaryMarkerUpper.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualPhysicalMarkerSearch

/-!
# Actual upper heights of stationary effective markers

The effective read coincides in row with the physical marker. Its true
immediate upper is supplied by the executed fill/contour seam and has the
same successor row as the actual source upper. No high-row restriction or
target numerical normality is needed. Raised markers instead have the
already proved direct numerical hit at their effective parent endpoint.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

theorem stationary_marker_upper_read (hLast : 1 < last)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent sourceUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hRight : p.root.column < parent.1.val)
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
  have hSame : F.height source = F.height parent :=
    (build_marked_parent p.reduced_build hMarkers hParent hMarked
      ((congrArg Ref.column hRootRef).trans_lt hRight)).2
  have hSourceUpperRow : md.upper.row = Row.bump md.current.row 0 := by
    rw [hUpperCell, hCurrent]
    change F.height sourceUpper = Row.bump (F.height source) 0
    change F.height sourceUpper = Row.B (F.height source) (F.height parent) at hB
    simpa only [← hSame, Row.B_self] using hB
  have hRoot : p.root.column ≤ md.sourceParent.column := by rw [hSourceParent]; exact hRight.le
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
theorem upper_height_of_stationary_marker (hLast : 1 < last)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent sourceUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hRight : p.root.column < parent.1.val)
    (hStationary : copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source)
    (hSourceUpper : (Frame.ofMountain p.reduced).upper source = some sourceUpper)
    {target targetUpper : (Frame.ofMountain result).Node}
    (hTargetRef : Frame.ref target = copy.outputRef)
    (hTargetUpper : (Frame.ofMountain result).upper target = some targetUpper) :
    (Frame.ofMountain result).height targetUpper = (Frame.ofMountain p.reduced).height sourceUpper := by
  obtain ⟨upperCell, hRead, hRow⟩ := copy.stationary_marker_upper_read
    hLast hMarked hParent hRight hStationary hSourceUpper
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hRead
  have he : upper = targetUpper := Option.some.inj
    ((Frame.upper_of_refs hTargetRef hUpperRef).symm.trans hTargetUpper)
  rw [← he, Frame.height, hUpperCell]
  exact hRow

/-- The raised effective endpoint's executed direct Q/P searches in typed
form. This is the raised-marker alternative to stationary upper preservation. -/
theorem raised_marker_parent_typed (hLast : 1 < last) (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent : (Frame.ofMountain p.reduced).Node}
    (parentCopy : EffectiveCopyOccurrence p block start references parent result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hRight : p.root.column < parent.1.val)
    (hRaised : (Frame.ofMountain p.reduced).height source < copy.read.outputCell.row)
    {target targetParent : (Frame.ofMountain result).Node}
    (hTargetRef : Frame.ref target = copy.outputRef)
    (hParentRef : Frame.ref targetParent = parentCopy.outputRef) :
    (Frame.ofMountain result).Q target = some targetParent ∧
      (Frame.ofMountain result).P target = some targetParent := by
  obtain ⟨hQ, hP⟩ := copy.raised_marker_search hLast hValid hMarked parentCopy hParent hRight hRaised
  exact ⟨(Executable.nextCandidate_ref_iff hValid.toOrdered target targetParent).mp
      (by simpa only [hTargetRef, hParentRef] using hQ),
    (Executable.findParent_ref_iff hValid.toOrdered target targetParent).mp
      (by simpa only [hTargetRef, hParentRef] using hP)⟩

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.stationary_marker_upper_read
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.upper_height_of_stationary_marker
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.raised_marker_parent_typed
