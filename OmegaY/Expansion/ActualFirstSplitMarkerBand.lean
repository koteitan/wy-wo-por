/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFirstSplitMarkerBand.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFirstSplitAll
import OmegaY.Expansion.ActualMixedBandDepthComparison

/-!
# Every event inside the first-split marker band has the right strict order

The preceding equal source depths recover a genuine common predecessor
parent. Its actual simultaneous advance supplies the new common row and Q.
At least one new source frontier is marked. Both-marked bands preserve
relative depth, while mixed source geometry forces the marked node to be
the deeper one. The mixed band bound uses only the already recognized
complete block-start prefix. The effective endpoints are included.

Cuts below the physical new row are handled by the separate stable-interval
theorem. This module does not by itself cover all earlier target events.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

private theorem unmarked_index_of_not_bucket
    {front : List Nat} {last : Nat} (p : Preparation front last)
    (node : (Frame.ofMountain p.reduced).Node)
    (hNot : ¬ BucketMem p.marked node.1.val (Frame.ref node)) :
    node.2.val ∉ (p.marked[node.1.val]?.getD []).map Ref.index := by
  intro h
  obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
  have he : marker = Frame.ref node := congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
  exact hNot (he ▸ hm)

theorem DynamicBlockState.first_split_marker_band_depth_lt
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent)
    {previous event targetEvent : Nat} (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) ambient)
    (hCommon : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hStart : previous + 1 ≤ event) (hEvent : event ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hEarlier : ∀ r, previous + 1 ≤ r → r < event →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) r) left.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) r) right.val)
    (hStrict : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) event) left.val <
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) event) right.val)
    (hMarked : BucketMem p.marked left.val
        (Frame.ref (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left)) ∨
      BucketMem p.marked right.val
        (Frame.ref (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right)))
    (hLow : (Frame.ofMountain p.reduced).eventCut event ≤ (Frame.ofMountain ambient).eventCut targetEvent)
    (hHigh : (Frame.ofMountain ambient).eventCut targetEvent ≤
      max leftCopy.read.outputCell.row rightCopy.read.outputCell.row) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        leftCopy.outputRef.column <
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        rightCopy.outputRef.column := by
  have hNormal := build_normal_of_success p.reduced_build
  let l := eventFrontier hNormal.toOrdered event left
  let r := eventFrontier hNormal.toOrdered event right
  have hLeftColumn : l.1 = left := (eventFrontier_spec hNormal.toOrdered event left).1
  have hRightColumn : r.1 = right := (eventFrontier_spec hNormal.toOrdered event right).1
  have hLeftFront : eventFrontier hNormal.toOrdered event l.1 = l := by rw [hLeftColumn]
  have hRightFront : eventFrontier hNormal.toOrdered event r.1 = r := by rw [hRightColumn]
  have hLeftBefore' : l.1.val < next := by simpa only [hLeftColumn] using hLeftBefore
  have hRightBefore' : r.1.val < next := by simpa only [hRightColumn] using hRightBefore
  have hBound : p.reduced.size - 1 < p.reduced.size := by omega
  have hLeftBound : left.val ≤ p.reduced.size - 1 := by
    have hc : left.val < p.reduced.size := left.isLt
    omega
  have hRightBound : right.val ≤ p.reduced.size - 1 := by
    have hc : right.val < p.reduced.size := right.isLt
    omega
  have hGeometry : (Frame.ofMountain p.reduced).height l = (Frame.ofMountain p.reduced).height r ∧
      ∃ candidate, (Frame.ofMountain p.reduced).Q l = some candidate ∧
        (Frame.ofMountain p.reduced).Q r = some candidate := by
    obtain ⟨before, parent, he, _, hb, hl, hr⟩ := build_first_split_previous_parent p.reduced_build
      hSourceWidth hBound left right hLeftBound hRightBound hCommon hStart hEvent hEarlier (ne_of_lt hStrict)
    obtain ⟨hRows, hLQ, hRQ⟩ := hNormal.common_parent_depth_split_geometry hSourceWidth hBound hb
      left right hLeftBound hRightBound hl hr (by simpa only [he] using ne_of_lt hStrict)
    exact ⟨by simpa only [l, r, he] using hRows, _,
      by simpa only [l, he] using hLQ, by simpa only [r, he] using hRQ⟩
  obtain ⟨hSameRow, candidate, hLeftQ, hRightQ⟩ := hGeometry
  have hCutOne := (Frame.ofMountain p.reduced).eventCut_one_le event
  by_cases hLeftMarked : BucketMem p.marked l.1.val (Frame.ref l)
  · by_cases hRightMarked : BucketMem p.marked r.1.val (Frame.ref r)
    · have hLQuery : referenceAt start references ((Frame.ofMountain p.reduced).height l) =
          .ok leftCopy.read.outputCell.row :=
        (leftCopy.state.referenceAt_preserved _).symm.trans (leftCopy.read.marked_reference hLeftMarked)
      have hRQuery : referenceAt start references ((Frame.ofMountain p.reduced).height r) =
          .ok rightCopy.read.outputCell.row :=
        (rightCopy.state.referenceAt_preserved _).symm.trans (rightCopy.read.marked_reference hRightMarked)
      have hTargetEq : leftCopy.read.outputCell.row = rightCopy.read.outputCell.row :=
        Except.ok.inj (hLQuery.symm.trans (by rw [hSameRow]; exact hRQuery))
      have hHigh' : (Frame.ofMountain ambient).eventCut targetEvent ≤ leftCopy.read.outputCell.row := by
        simpa only [← hTargetEq, max_self] using hHigh
      rcases lt_or_eq_of_le hHigh' with hInterior | hEndpoint
      · have hCompared := s.marked_band_depth_comparison history hLast hSourceWidth hTargetWidth
          hLeftBefore' hRightBefore' leftCopy rightCopy hLeftMarked hRightMarked
          hLeftFront hRightFront hLow hInterior
        exact hCompared.2.2.mp (by simpa only [hLeftColumn, hRightColumn] using hStrict)
      · have hLeftOwn : leftCopy.contourCut ((Frame.ofMountain p.reduced).eventCut event) =
            leftCopy.read.outputCell.row := by
          rw [leftCopy.marked_frontier_cut_eq hLeftMarked hCutOne hLeftFront]
          exact leftCopy.read.output_row.symm
        have hRightOwn : rightCopy.contourCut ((Frame.ofMountain p.reduced).eventCut event) =
            rightCopy.read.outputCell.row := by
          rw [rightCopy.marked_frontier_cut_eq hRightMarked hCutOne hRightFront]
          exact rightCopy.read.output_row.symm
        obtain ⟨_, leftNode, hLeftRef, _, hLeftOwnFront⟩ :=
          leftCopy.frontierAt_own_lift_of_marked s.ambient_valid hLeftMarked hCutOne hLeftFront
        obtain ⟨_, rightNode, hRightRef, _, hRightOwnFront⟩ :=
          rightCopy.frontierAt_own_lift_of_marked s.ambient_valid hRightMarked hCutOne hRightFront
        have hLeftActual : eventFrontier s.ambient_valid.toOrdered targetEvent leftNode.1 = leftNode := by
          change frontierAt s.ambient_valid.toOrdered _ _ _ = _
          simpa only [hEndpoint, hLeftOwn] using hLeftOwnFront
        have hRightActual : eventFrontier s.ambient_valid.toOrdered targetEvent rightNode.1 = rightNode := by
          change frontierAt s.ambient_valid.toOrdered _ _ _ = _
          simpa only [hEndpoint, hTargetEq, hRightOwn] using hRightOwnFront
        have hCompared := s.first_difference_depth_lt_at_frontiers history hLast hStartRun
          hSourceWidth hTargetWidth hLeftBefore' hRightBefore' leftCopy rightCopy hLeftRef hRightRef
          (by simpa only [hLeftColumn, hRightColumn] using hCommon) hStart hEvent
          (by simpa only [hLeftColumn, hRightColumn] using hEarlier)
          hLeftFront hRightFront hLeftActual hRightActual
          (by simpa only [hLeftColumn, hRightColumn] using hStrict)
        have hLeftOut : leftNode.1.val = leftCopy.outputRef.column := congrArg Ref.column hLeftRef
        have hRightOut : rightNode.1.val = rightCopy.outputRef.column := congrArg Ref.column hRightRef
        simpa only [hLeftOut, hRightOut] using hCompared
    · have hReal : Real l := (eventFrontier_spec hNormal.toOrdered event left).2.1
      obtain ⟨index, a⟩ := leftCopy.state.actual_marker_root_interval hLast hLeftMarked
        (Canonical.cellAt_of_frame_node p.reduced l)
        (Row.zero_lt_one.trans_le (one_le_height hNormal.toOrdered hReal))
      obtain ⟨a⟩ := a
      have hOpposite := a.mixed_source_event_depth_lt hSourceWidth hLeftMarked hRightMarked
        leftCopy.state.next_lower rightCopy.state.next_lower rfl hSameRow.symm hLeftQ hRightQ
        hLeftFront hRightFront
      rw [hLeftColumn, hRightColumn] at hOpposite
      exact False.elim ((not_lt_of_ge hStrict.le) hOpposite)
  · have hRightMarked : BucketMem p.marked r.1.val (Frame.ref r) := by
      rcases hMarked with hl | hr
      · exact False.elim (hLeftMarked (by simpa only [hLeftColumn] using hl))
      · simpa only [hRightColumn] using hr
    have hLeftUnmarked := unmarked_index_of_not_bucket p l hLeftMarked
    have hStationary := leftCopy.stationary_at_marker_row hLast hLeftUnmarked hRightMarked hSameRow
    have hTargets : leftCopy.read.outputCell.row ≤ rightCopy.read.outputCell.row := by
      rw [hStationary, hSameRow]
      exact rightCopy.read.source_row_le_output
    have hHigh' : (Frame.ofMountain ambient).eventCut targetEvent ≤ rightCopy.read.outputCell.row := by
      simpa only [max_eq_right hTargets] using hHigh
    exact s.mixed_band_depth_lt_of_left_recognition history hLast hStartRun hSourceWidth hTargetWidth
      hKnown hRightBefore' hLeftBefore' rightCopy leftCopy hRightMarked hLeftUnmarked
      hSameRow.symm hRightQ hLeftQ hEvent hRightFront hLeftFront hLow hHigh'

 /-- The physical source row itself is a real output event with the strict
comparison. Thus one need not wait for the higher effective endpoints. -/
theorem DynamicBlockState.first_split_marker_physical_event
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent)
    {previous event : Nat} (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) ambient)
    (hCommon : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hStart : previous + 1 ≤ event) (hEvent : event ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hEarlier : ∀ r, previous + 1 ≤ r → r < event →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) r) left.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) r) right.val)
    (hStrict : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) event) left.val <
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) event) right.val)
    (hMarked : BucketMem p.marked left.val
        (Frame.ref (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left)) ∨
      BucketMem p.marked right.val
        (Frame.ref (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right))) :
    ∃ targetEvent,
      targetEvent ≤ (Frame.ofMountain ambient).lastEvent ∧
      (Frame.ofMountain ambient).eventCut targetEvent = (Frame.ofMountain p.reduced).eventCut event ∧
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
          leftCopy.outputRef.column <
        parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
          rightCopy.outputRef.column := by
  have hNormal := build_normal_of_success p.reduced_build
  have hCut := (Frame.ofMountain p.reduced).eventCut_one_le event
  have hLeftColumn := (eventFrontier_spec hNormal.toOrdered event left).1
  have hRightColumn := (eventFrontier_spec hNormal.toOrdered event right).1
  have hPhysical : ∃ targetEvent,
      targetEvent ≤ (Frame.ofMountain ambient).lastEvent ∧
      (Frame.ofMountain ambient).eventCut targetEvent = (Frame.ofMountain p.reduced).eventCut event ∧
      (Frame.ofMountain p.reduced).eventCut event ≤
        max leftCopy.read.outputCell.row rightCopy.read.outputCell.row := by
    rcases hMarked with hl | hr
    · have hMark : BucketMem p.marked
          (eventFrontier hNormal.toOrdered event left).1.val
          (Frame.ref (eventFrontier hNormal.toOrdered event left)) := by simpa only [hLeftColumn] using hl
      have hFront : eventFrontier hNormal.toOrdered event
          (eventFrontier hNormal.toOrdered event left).1 = eventFrontier hNormal.toOrdered event left := by
        rw [hLeftColumn]
      obtain ⟨physical⟩ := leftCopy.physical_marker_read hMark
      obtain ⟨targetEvent, node, hEnd, hRow, _⟩ := physical.actual_event_at_source_cut
        s.ambient_valid hMark hCut hFront
      have hSourceRow := leftCopy.marked_frontier_cut_eq hMark hCut hFront
      refine ⟨targetEvent, hEnd, hRow, ?_⟩
      rw [hSourceRow]
      exact leftCopy.read.source_row_le_output.trans (le_max_left _ _)
    · have hMark : BucketMem p.marked
          (eventFrontier hNormal.toOrdered event right).1.val
          (Frame.ref (eventFrontier hNormal.toOrdered event right)) := by simpa only [hRightColumn] using hr
      have hFront : eventFrontier hNormal.toOrdered event
          (eventFrontier hNormal.toOrdered event right).1 = eventFrontier hNormal.toOrdered event right := by
        rw [hRightColumn]
      obtain ⟨physical⟩ := rightCopy.physical_marker_read hMark
      obtain ⟨targetEvent, node, hEnd, hRow, _⟩ := physical.actual_event_at_source_cut
        s.ambient_valid hMark hCut hFront
      have hSourceRow := rightCopy.marked_frontier_cut_eq hMark hCut hFront
      refine ⟨targetEvent, hEnd, hRow, ?_⟩
      rw [hSourceRow]
      exact rightCopy.read.source_row_le_output.trans (le_max_right _ _)
  obtain ⟨targetEvent, hEnd, hRow, hBelow⟩ := hPhysical
  exact ⟨targetEvent, hEnd, hRow,
    s.first_split_marker_band_depth_lt history hLast hStartRun hSourceWidth hTargetWidth hKnown
      left right hLeftBefore hRightBefore leftCopy rightCopy hCommon hStart hEvent hEarlier hStrict hMarked
      hRow.ge (hRow.trans_le hBelow)⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.first_split_marker_band_depth_lt
#print axioms OmegaY.Expansion.DynamicBlockState.first_split_marker_physical_event
