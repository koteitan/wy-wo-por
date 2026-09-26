/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFirstSplitComparison.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFirstSplitEvent
import OmegaY.Expansion.ActualFirstDifferenceDepth

/-!+# A strict actual target comparison at a nonmarker first difference

Source numerical recovery, executed contour synchronization and all four
parent exits are combined. The target event and both target frontiers are
constructed internally. Only the two current source frontiers' nonmarker
status remains as the event-synchronization branch condition. Earlier
inserted target events and marked first-difference transitions are not
covered by this pointwise strict comparison.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem DynamicBlockState.actual_first_split_depth_lt
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {previous event : Nat}
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) ambient)
    (hLeftUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left).2.val ∉
      (p.marked[left.val]?.getD []).map Ref.index)
    (hRightUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right).2.val ∉
      (p.marked[right.val]?.getD []).map Ref.index)
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
        hSourceWidth (p.reduced.size - 1) event) right.val) :
    ∃ data : EffectiveSameRowEvent leftCopy rightCopy s.ambient_valid,
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) data.event)
          data.uNode.1.val <
        parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) data.event)
          data.zNode.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  have hBound : p.reduced.size - 1 < p.reduced.size := by omega
  have hLB : left.val ≤ p.reduced.size - 1 := by have hc : left.val < p.reduced.size := left.isLt; omega
  have hRB : right.val ≤ p.reduced.size - 1 := by have hc : right.val < p.reduced.size := right.isLt; omega
  obtain ⟨data⟩ := s.actual_first_split_event history hLast hSourceWidth hBound left right hLB hRB
    hLeftBefore hRightBefore leftCopy rightCopy hLeftUnmarked hRightUnmarked hCommon hStart hEvent
    hEarlier (ne_of_lt hStrict)
  have hLeftCol := (eventFrontier_spec hNormal.toOrdered event left).1
  have hRightCol := (eventFrontier_spec hNormal.toOrdered event right).1
  refine ⟨data, s.first_difference_depth_lt_at_frontiers history hLast hStartRun hSourceWidth hTargetWidth
    (by simpa only [hLeftCol] using hLeftBefore) (by simpa only [hRightCol] using hRightBefore)
    leftCopy rightCopy data.u_ref data.z_ref ?_ hStart hEvent ?_ ?_ ?_ data.u_frontier data.z_frontier ?_⟩
  · simpa only [hLeftCol, hRightCol] using hCommon
  · simpa only [hLeftCol, hRightCol] using hEarlier
  · rw [hLeftCol]
  · rw [hRightCol]
  · simpa only [hLeftCol, hRightCol] using hStrict

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_first_split_depth_lt
