/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSharedContourCutAll.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSharedContourCut
import OmegaY.Expansion.ActualMarkedFrontierCopy
import OmegaY.Expansion.CommonMarkerBlocker
import OmegaY.Expansion.ActualFixedEffectiveParent

/-!+# All source-marker cases of actual shared contour cuts

Two source frontiers at one cut with a common actual source parent are
either both marked or both unmarked. Marked frontiers have exactly the
source cut as their own row, and the common block-start reference query
then makes their lifted cuts equal. Thus the actual shared-event packet
has no source-marker exclusion. This remains a pointwise common-current-P
theorem, not a global sampling at a first differing parent forest.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem source_marked_index_iff {front : List Nat} {last : Nat}
    (p : Preparation front last) (node : (Frame.ofMountain p.reduced).Node) :
    node.2.val ∈ (p.marked[node.1.val]?.getD []).map Ref.index ↔
      BucketMem p.marked node.1.val (Frame.ref node) := by
  constructor
  · intro h
    obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
    have hc := (p.marker_iff.mp hm).1
    have he : marker = Frame.ref node := congrArg₂ Ref.mk hc hi
    exact he ▸ hm
  · intro h
    exact List.mem_map.mpr ⟨Frame.ref node, h, rfl⟩

/-- Simultaneous marker membership at a single actual source cut, with
the good-parent case excluded by the real prepared marker computation. -/
theorem Preparation.common_parent_marked_iff_at_cut
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {u z parent : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    BucketMem p.marked u.1.val (Frame.ref u) ↔ BucketMem p.marked z.1.val (Frame.ref z) := by
  by_cases hFixed : parent.1.val < p.root.column
  · exact iff_of_false (p.fixed_parent_not_marked hUP hFixed) (p.fixed_parent_not_marked hZP hFixed)
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  have hRootColumn : root.1.val = p.root.column := congrArg Ref.column hRootRef
  have hRight : root.1.val ≤ parent.1.val := by omega
  obtain ⟨uUpper, hUUpper⟩ := hNormal.upper_of_parent hUP
  obtain ⟨zUpper, hZUpper⟩ := hNormal.upper_of_parent hZP
  have hu := frontierAt_spec hNormal.toOrdered hCut u.1
  have hz := frontierAt_spec hNormal.toOrdered hCut z.1
  have huBelow : (Frame.ofMountain p.reduced).height u ≤ cut := hUFront ▸ hu.2.2.1
  have hzBelow : (Frame.ofMountain p.reduced).height z ≤ cut := hZFront ▸ hz.2.2.1
  have huAbove := hu.2.2.2.2 uUpper (hUFront.symm ▸ hUUpper)
  have hzAbove := hz.2.2.2.2 zUpper (hZFront.symm ▸ hZUpper)
  rcases le_total ((Frame.ofMountain p.reduced).height z) ((Frame.ofMountain p.reduced).height u) with hle | hle
  · exact build_common_parent_marker_iff p.reduced_build hMarkers hUP hZP hZUpper hle
      (huBelow.trans_lt hzAbove) hRight
  · exact (build_common_parent_marker_iff p.reduced_build hMarkers hZP hUP hUUpper hle
      (hzBelow.trans_lt huAbove) hRight).symm

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {u z : (Frame.ofMountain p.reduced).Node}
  (uCopy : EffectiveCopyOccurrence p block start references u result)
  (zCopy : EffectiveCopyOccurrence p block start references z result)

/-- Two actual marked frontiers at a shared source cut have equal own
cuts. Their reference queries may run at different copy times, but each
is the unchanged query of the same fixed block-start map. -/
theorem contourCut_eq_of_marked_frontiers
    (hUMarked : BucketMem p.marked u.1.val (Frame.ref u))
    (hZMarked : BucketMem p.marked z.1.val (Frame.ref z))
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    uCopy.contourCut cut = zCopy.contourCut cut := by
  have hUCut := uCopy.marked_frontier_cut_eq hUMarked hCut hUFront
  have hZCut := zCopy.marked_frontier_cut_eq hZMarked hCut hZFront
  have hUReference : referenceAt start references ((Frame.ofMountain p.reduced).height u) =
      .ok uCopy.read.outputCell.row :=
    (uCopy.state.referenceAt_preserved _).symm.trans (uCopy.read.marked_reference hUMarked)
  have hZReference : referenceAt start references ((Frame.ofMountain p.reduced).height z) =
      .ok zCopy.read.outputCell.row :=
    (zCopy.state.referenceAt_preserved _).symm.trans (zCopy.read.marked_reference hZMarked)
  rw [← hUCut] at hUReference
  rw [← hZCut] at hZReference
  have hRows := Except.ok.inj (hUReference.symm.trans hZReference)
  have hUOutput : uCopy.read.outputCell.row = uCopy.contourCut cut := by
    rw [uCopy.read.output_row, hUCut]
    rfl
  have hZOutput : zCopy.read.outputCell.row = zCopy.contourCut cut := by
    rw [zCopy.read.output_row, hZCut]
    rfl
  exact hUOutput.symm.trans (hRows.trans hZOutput)

theorem shared_contour_frontier_of_marked (hValid : MountainValid result)
    (hUMarked : BucketMem p.marked u.1.val (Frame.ref u))
    (hZMarked : BucketMem p.marked z.1.val (Frame.ref z))
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    Nonempty (SharedContourFrontier uCopy zCopy cut hValid) := by
  have hSame := uCopy.contourCut_eq_of_marked_frontiers zCopy hUMarked hZMarked hCut hUFront hZFront
  obtain ⟨hUCut, uNode, hURef, hUCell, hUOwn⟩ :=
    uCopy.frontierAt_own_lift_of_marked hValid hUMarked hCut hUFront
  obtain ⟨hZCut, zNode, hZRef, hZCell, hZOwn⟩ :=
    zCopy.frontierAt_own_lift_of_marked hValid hZMarked hCut hZFront
  have hShared : (1 : Row) ≤ max (uCopy.contourCut cut) (zCopy.contourCut cut) :=
    hUCut.trans (le_max_left _ _)
  have hSharedEq : max (uCopy.contourCut cut) (zCopy.contourCut cut) = uCopy.contourCut cut :=
    max_eq_left hSame.ge
  have hUShared : frontierAt hValid.toOrdered (max (uCopy.contourCut cut) (zCopy.contourCut cut))
      hShared uNode.1 = uNode := by simpa only [hSharedEq] using hUOwn
  have hZShared : frontierAt hValid.toOrdered (max (uCopy.contourCut cut) (zCopy.contourCut cut))
      hShared zNode.1 = zNode := by simpa only [hSame, max_self] using hZOwn
  obtain ⟨event, hEvent, hBelow, hMax, hFrontiers⟩ := event_floor_at_cut hValid.toOrdered hShared
  exact ⟨⟨hUCut, hZCut, hShared, uNode, zNode, hURef, hZRef, hUCell, hZCell,
    hUOwn, hZOwn, hUShared, hZShared, event, hEvent, hBelow, hMax, hFrontiers⟩⟩

/-- Complete pointwise common-cut coverage: marker membership and row
order are decided inside the theorem. The current designated source P
equality remains essential, rather than equality only in a prior forest. -/
theorem shared_contour_frontier_all (hLast : 1 < last) (hValid : MountainValid result)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    Nonempty (SharedContourFrontier uCopy zCopy cut hValid) := by
  have hIff := p.common_parent_marked_iff_at_cut hUP hZP hCut hUFront hZFront
  by_cases hUMarked : BucketMem p.marked u.1.val (Frame.ref u)
  · exact uCopy.shared_contour_frontier_of_marked zCopy hValid hUMarked (hIff.mp hUMarked)
      hCut hUFront hZFront
  · have hZMarked : ¬ BucketMem p.marked z.1.val (Frame.ref z) := fun hz => hUMarked (hIff.mpr hz)
    exact uCopy.shared_contour_frontier zCopy hLast hValid
      (fun hu => hUMarked ((source_marked_index_iff p u).mp hu))
      (fun hz => hZMarked ((source_marked_index_iff p z).mp hz)) hUP hZP hCut hUFront hZFront

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.common_parent_marked_iff_at_cut
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.contourCut_eq_of_marked_frontiers
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.shared_contour_frontier_of_marked
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.shared_contour_frontier_all
