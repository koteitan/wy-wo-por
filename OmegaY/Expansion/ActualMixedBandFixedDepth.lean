/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMixedBandFixedDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMixedMarkerFrontier
import OmegaY.Expansion.ActualBoundaryDepthComparison

/-!
# The stationary side throughout a genuine mixed marker band

For same-row source frontiers with the same geometric candidate, exactly
one marked, the unmarked copy is the actual frontier at every event from
the source row through the other column's effective target. Its source
parent is absent or strictly in the fixed good part, so its absolute raw
event depth is unchanged throughout this whole interval.

The varying depth in the marked band is not bounded by this module.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem EffectiveCopyOccurrence.unmarked_frontier_in_mixed_band
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {marked other candidate : (Frame.ofMountain p.reduced).Node}
    (markedCopy : EffectiveCopyOccurrence p block start references marked result)
    (otherCopy : EffectiveCopyOccurrence p block start references other result)
    (hLast : 1 < last) (hValid : MountainValid result)
    (hMarked : BucketMem p.marked marked.1.val (Frame.ref marked))
    (hUnmarked : other.2.val ∉ (p.marked[other.1.val]?.getD []).map Ref.index)
    (hSameRow : (Frame.ofMountain p.reduced).height marked = (Frame.ofMountain p.reduced).height other)
    (hMarkedQ : (Frame.ofMountain p.reduced).Q marked = some candidate)
    (hOtherQ : (Frame.ofMountain p.reduced).Q other = some candidate)
    {sourceEvent targetEvent : Nat}
    (hMarkedFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent marked.1 = marked)
    (hOtherFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent other.1 = other)
    (hLow : (Frame.ofMountain p.reduced).eventCut sourceEvent ≤ (Frame.ofMountain result).eventCut targetEvent)
    (hHigh : (Frame.ofMountain result).eventCut targetEvent ≤ markedCopy.read.outputCell.row) :
    ∃ node : (Frame.ofMountain result).Node,
      Frame.ref node = otherCopy.outputRef ∧
      (Frame.ofMountain result).cell node = otherCopy.read.outputCell ∧
      eventFrontier hValid.toOrdered targetEvent node.1 = node := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hCut := F.eventCut_one_le sourceEvent
  obtain ⟨shared⟩ := markedCopy.shared_contour_frontier_mixed_candidate otherCopy hLast hValid
    hMarked hUnmarked hSameRow hMarkedQ hOtherQ hCut hMarkedFront hOtherFront
  have hCutRow := markedCopy.marked_frontier_cut_eq hMarked hCut hMarkedFront
  have hStationary := otherCopy.stationary_at_marker_row hLast hUnmarked hMarked hSameRow.symm
  have hMarkedTarget : markedCopy.contourCut (F.eventCut sourceEvent) = markedCopy.read.outputCell.row := by
    rw [hCutRow]
    exact markedCopy.read.output_row.symm
  have hNodeRow : G.height shared.zNode = F.eventCut sourceEvent := by
    change (G.cell shared.zNode).row = F.eventCut sourceEvent
    rw [shared.z_cell, hStationary, ← hSameRow, ← hCutRow]
  refine ⟨shared.zNode, shared.z_ref, shared.z_cell, ?_⟩
  apply frontierAt_eq_of_upper_barrier hValid.toOrdered (G.eventCut_one_le targetEvent)
  · exact hNodeRow.trans_le hLow
  · intro upper hUpper
    have hAtShared := frontierAt_spec hValid.toOrdered shared.shared_cut_one shared.zNode.1
    have hBarrier := hAtShared.2.2.2.2 upper (shared.z_shared.symm ▸ hUpper)
    exact (hHigh.trans (hMarkedTarget ▸ le_max_left _ _)).trans_lt hBarrier

theorem DynamicBlockState.mixed_band_unmarked_depth_eq
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {marked other candidate : (Frame.ofMountain p.reduced).Node}
    (hOtherBefore : other.1.val < next)
    (markedCopy : EffectiveCopyOccurrence p block start references marked ambient)
    (otherCopy : EffectiveCopyOccurrence p block start references other ambient)
    (hMarked : BucketMem p.marked marked.1.val (Frame.ref marked))
    (hUnmarked : other.2.val ∉ (p.marked[other.1.val]?.getD []).map Ref.index)
    (hSameRow : (Frame.ofMountain p.reduced).height marked = (Frame.ofMountain p.reduced).height other)
    (hMarkedQ : (Frame.ofMountain p.reduced).Q marked = some candidate)
    (hOtherQ : (Frame.ofMountain p.reduced).Q other = some candidate)
    {sourceEvent targetEvent : Nat} (hEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hMarkedFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent marked.1 = marked)
    (hOtherFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent other.1 = other)
    (hLow : (Frame.ofMountain p.reduced).eventCut sourceEvent ≤ (Frame.ofMountain ambient).eventCut targetEvent)
    (hHigh : (Frame.ofMountain ambient).eventCut targetEvent ≤ markedCopy.read.outputCell.row) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        otherCopy.outputRef.column =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) sourceEvent) other.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨node, hRef, _, hFront⟩ := markedCopy.unmarked_frontier_in_mixed_band otherCopy hLast
    s.ambient_valid hMarked hUnmarked hSameRow hMarkedQ hOtherQ hMarkedFront hOtherFront hLow hHigh
  have hExit : (Frame.ofMountain p.reduced).P other = none ∨
      ∃ parent, (Frame.ofMountain p.reduced).P other = some parent ∧ parent.1.val < p.root.column := by
    cases hParent : (Frame.ofMountain p.reduced).P other with
    | none => exact Or.inl rfl
    | some parent =>
      have hReal : Real marked := hMarkedFront ▸
        (eventFrontier_spec hNormal.toOrdered sourceEvent marked.1).2.1
      obtain ⟨index, a⟩ := markedCopy.state.actual_marker_root_interval hLast hMarked
        (Canonical.cellAt_of_frame_node p.reduced marked)
        (Row.zero_lt_one.trans_le (one_le_height hNormal.toOrdered hReal))
      obtain ⟨a⟩ := a
      have hNotMarked : ¬ BucketMem p.marked other.1.val (Frame.ref other) := by
        intro hm
        exact hUnmarked (List.mem_map.mpr ⟨Frame.ref other, hm, rfl⟩)
      have hFixed := (a.mixed_candidate_parent_exit hMarked hNotMarked
        markedCopy.state.next_lower otherCopy.state.next_lower rfl hSameRow.symm
        hMarkedQ hOtherQ hParent).2
      exact Or.inr ⟨parent, rfl, hFixed⟩
  have hDepth := s.depth_eq_of_terminal_or_fixed_parent history hLast hStartRun hSourceWidth hTargetWidth
    otherCopy.state.next_lower hOtherBefore otherCopy hEvent hOtherFront hRef hFront hExit
  have hColumn : node.1.val = otherCopy.outputRef.column := congrArg Ref.column hRef
  simpa only [hColumn] using hDepth

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.unmarked_frontier_in_mixed_band
#print axioms OmegaY.Expansion.DynamicBlockState.mixed_band_unmarked_depth_eq
