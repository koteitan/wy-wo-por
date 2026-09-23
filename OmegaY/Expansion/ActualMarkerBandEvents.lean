/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkerBandEvents.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CommonMarkerBandEvents
import OmegaY.Expansion.ActualSharedContourCutAll

/-!+# Inserted-event depth equality from actual common source markers

Both finished bands and all their shared reference cells are reconstructed
from independent real effective occurrences. Complete preservation into
one result supplies the earlier/later ambient relation. Every actual event
between the physical source row and the effective target row consequently
has equal raw depths in the two columns. No band or target parent-equality
certificate is required from the caller.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {u z : (Frame.ofMountain p.reduced).Node}
  (uCopy : EffectiveCopyOccurrence p block start references u result)
  (zCopy : EffectiveCopyOccurrence p block start references z result)

theorem actual_common_marker_band_event_depth_eq
    (hLast : 1 < last) (hValid : MountainValid result) (hWidth : 0 < result.size)
    (hColumn : z.1.val ≤ u.1.val)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hMarked : BucketMem p.marked u.1.val (Frame.ref u))
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z)
    {event : Nat} (hLow : cut ≤ (Frame.ofMountain result).eventCut event)
    (hHigh : (Frame.ofMountain result).eventCut event < uCopy.read.outputCell.row) :
    parentDepth (eventParentMap hValid.toOrdered hWidth (result.size - 1) event) uCopy.outputRef.column =
      parentDepth (eventParentMap hValid.toOrdered hWidth (result.size - 1) event) zCopy.outputRef.column := by
  let F := Frame.ofMountain p.reduced
  let du := uCopy.data
  let dz := zCopy.data
  let mu := du.marker_data (Frame.ref u) hMarked
  have hNormal := build_normal_of_success p.reduced_build
  have hZMarked := (p.common_parent_marked_iff_at_cut hUP hZP hCut hUFront hZFront).mp hMarked
  have hUCut := uCopy.marked_frontier_cut_eq hMarked hCut hUFront
  have hZCut := zCopy.marked_frontier_cut_eq hZMarked hCut hZFront
  have hRight : p.root.column ≤ parent.1.val := by
    by_contra hn
    exact p.fixed_parent_not_marked hUP (Nat.lt_of_not_ge hn) hMarked
  obtain ⟨zUpper, hZUpper⟩ := hNormal.upper_of_parent hZP
  have hOrder : F.height z ≤ F.height u := (hZCut.symm.trans hUCut).le
  have hOverlap : F.height u < F.height zUpper := by
    rw [← hUCut]
    exact (frontierAt_spec hNormal.toOrdered hCut z.1).2.2.2.2 zUpper (hZFront.symm ▸ hZUpper)
  have hUSource : p.reduced[u.1.val]? = some du.sources :=
    (uCopy.state.base_ambient _ u.1.isLt).symm.trans du.source_column
  have hZSource : p.reduced[z.1.val]? = some dz.sources :=
    (zCopy.state.base_ambient _ z.1.isLt).symm.trans dz.source_column
  obtain ⟨_, hUPP, hUPL⟩ := uCopy.state.column_data_parent_inputs hLast u.1.isLt du
  obtain ⟨_, hZPP, hZPL⟩ := zCopy.state.column_data_parent_inputs hLast z.1.isLt dz
  have hSize : zCopy.before.size ≤ uCopy.before.size := by
    have hu := du.destination
    have hz := dz.destination
    omega
  have hUPreserve : PreservesColumns uCopy.before result :=
    (PreservesColumns.push uCopy.before uCopy.column).trans uCopy.preserved
  have hZPreserve : PreservesColumns zCopy.before result :=
    (PreservesColumns.push zCopy.before zCopy.column).trans zCopy.preserved
  have hPreserve : PreservesColumns zCopy.before uCopy.before := by
    intro column hc
    exact (hUPreserve column (hc.trans_le hSize)).symm.trans (hZPreserve column hc)
  have hRefs : ∀ ref ∈ references, ValidRef zCopy.before ref := by
    intro ref hRef
    exact zCopy.state.start_preserved.validRef
      (RootRowsInColumn.references_valid zCopy.state.boundary_rows zCopy.state.reference_map ref hRef)
  obtain ⟨rootNodes, hRootNodes, hRootRead⟩ := Canonical.cellAt_ok_iff.mp p.restored_root
  obtain ⟨hRootColumnBound, hRootColumnEq⟩ := Array.getElem?_eq_some_iff.mp hRootNodes
  have hRootIndex : p.root.index < p.reduced[p.root.column].size := by
    rw [hRootColumnEq]
    exact (Array.getElem?_eq_some_iff.mp hRootRead).1
  let root : F.Node := ⟨⟨p.root.column, hRootColumnBound⟩, ⟨p.root.index, hRootIndex⟩⟩
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := p.markers_built
  obtain ⟨pair⟩ := build_common_parent_marker_bands p.reduced_build hMarkers hUP hZP hZUpper hOrder hOverlap
    hRight du dz hUSource hZSource hUPP hUPL hZPP hZPL hPreserve hRefs
      uCopy.read.copy_run zCopy.read.copy_run hMarked
  obtain ⟨_, _, hURow, _, _⟩ := build_common_parent_marker_rows p.reduced_build hMarkers
    hUP hZP hZUpper hOrder hOverlap hRight (.inl hMarked)
  have hParentRow : F.height parent = cut := hURow.symm.trans hUCut.symm
  have hCurrent : mu.current = F.cell u := Option.some.inj (mu.current_at.symm.trans uCopy.read.source_at)
  have hReference := uCopy.read.marked_reference hMarked
  have hTarget : mu.targetCell.row = uCopy.read.outputCell.row :=
    Except.ok.inj (mu.reference.symm.trans (by simpa only [hCurrent] using hReference))
  have hUResult : result[uCopy.before.size]? = some uCopy.column := uCopy.preserved.column_read (by simp)
  have hZResult : result[zCopy.before.size]? = some zCopy.column := zCopy.preserved.column_read (by simp)
  have hUResultBound := (Array.getElem?_eq_some_iff.mp hUResult).1
  have hZResultBound := (Array.getElem?_eq_some_iff.mp hZResult).1
  let uc : Fin (Frame.ofMountain result).width := ⟨uCopy.before.size, hUResultBound⟩
  let zc : Fin (Frame.ofMountain result).width := ⟨zCopy.before.size, hZResultBound⟩
  exact pair.event_depth_eq hValid uc zc hUResult hZResult hWidth (by omega)
    (by change uCopy.before.size ≤ result.size - 1; omega)
    (by change zCopy.before.size ≤ result.size - 1; omega)
    (hParentRow.le.trans hLow) (hHigh.trans_eq hTarget.symm)

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.actual_common_marker_band_event_depth_eq
