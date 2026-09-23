/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNonmarkerSplitComparison.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNonmarkerSplitEvent
import OmegaY.Expansion.ActualForkDepthComparison

/-!+# Actual strict comparison at a nonmarker source split

The common target event is constructed, rather than supplied. The previous
source event has a common parent and the next event has a strict depth
order. Actual history supplies the old occurrences; unmarked new source
frontiers yield the shared event. Source nearest-smaller nesting and the
recorded copied paths then transfer the strict depth order to that event.

The shallower new source parent is strictly right of the root. This is one
actual first-split branch, not a complete depth-word sampling theorem.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem DynamicBlockState.actual_nonmarker_split_comparison
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {event : Nat} (hEvent : event < (Frame.ofMountain p.reduced).lastEvent)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) left) ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) right) ambient)
    (hLeftUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) left).2.val ∉
      (p.marked[left.val]?.getD []).map Ref.index)
    (hRightUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) right).2.val ∉
      (p.marked[right.val]?.getD []).map Ref.index)
    {oldParent ancestor : (Frame.ofMountain p.reduced).Node}
    (hOldLeft : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) = some oldParent)
    (hOldRight : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) = some oldParent)
    (hParent : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) left) = some ancestor)
    (hAncestorRight : p.root.column < ancestor.1.val)
    (hStrict : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) (event + 1)) left.val <
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) (event + 1)) right.val) :
    ∃ data : EffectiveSameRowEvent leftCopy rightCopy s.ambient_valid,
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) data.event)
          data.uNode.1.val <
        parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) data.event)
          data.zNode.1.val ∧
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) data.event)
          data.uNode.1.val +
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
          hSourceWidth (p.reduced.size - 1) (event + 1)) right.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
          hSourceWidth (p.reduced.size - 1) (event + 1)) left.val +
        parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) data.event)
          data.zNode.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  have hOldLCol := (eventFrontier_spec hNormal.toOrdered event left).1
  have hOldRCol := (eventFrontier_spec hNormal.toOrdered event right).1
  have hNewLCol := (eventFrontier_spec hNormal.toOrdered (event + 1) left).1
  have hNewRCol := (eventFrontier_spec hNormal.toOrdered (event + 1) right).1
  have hLeftRight : p.root.column < left.val := by simpa only [hNewLCol] using leftCopy.state.next_lower
  have hRightRight : p.root.column < right.val := by simpa only [hNewRCol] using rightCopy.state.next_lower
  obtain ⟨oldLeftCopy⟩ := s.prior_effective_occurrence history hLast
    (show p.root.column < (eventFrontier hNormal.toOrdered event left).1.val by simpa only [hOldLCol] using hLeftRight)
    (show (eventFrontier hNormal.toOrdered event left).1.val < next by simpa only [hOldLCol] using hLeftBefore)
  obtain ⟨oldRightCopy⟩ := s.prior_effective_occurrence history hLast
    (show p.root.column < (eventFrontier hNormal.toOrdered event right).1.val by simpa only [hOldRCol] using hRightRight)
    (show (eventFrontier hNormal.toOrdered event right).1.val < next by simpa only [hOldRCol] using hRightBefore)
  have hBound : p.reduced.size - 1 < p.reduced.size := by omega
  have hlb : left.val ≤ p.reduced.size - 1 := by have := left.isLt; change left.val < p.reduced.size at this; omega
  have hrb : right.val ≤ p.reduced.size - 1 := by have := right.isLt; change right.val < p.reduced.size at this; omega
  obtain ⟨data⟩ := actual_nonmarker_split_event hLast s.ambient_valid hSourceWidth hBound hEvent
    left right hlb hrb oldLeftCopy oldRightCopy leftCopy rightCopy hLeftUnmarked hRightUnmarked
    hOldLeft hOldRight (ne_of_lt hStrict)
  have hCommon : (Frame.ofMountain p.reduced).P
      (eventFrontier hNormal.toOrdered event (eventFrontier hNormal.toOrdered (event + 1) left).1) =
    (Frame.ofMountain p.reduced).P
      (eventFrontier hNormal.toOrdered event (eventFrontier hNormal.toOrdered (event + 1) right).1) := by
    rw [hNewLCol, hNewRCol]
    exact hOldLeft.trans hOldRight.symm
  have hCompare := s.first_difference_copied_parent_comparison history hLast hStartRun hSourceWidth hTargetWidth
    hParent hAncestorRight (by simpa only [hNewLCol] using hLeftBefore)
    (by simpa only [hNewRCol] using hRightBefore) leftCopy rightCopy data.u_ref data.z_ref
    hCommon le_rfl (by omega) (by intro r hr hre; omega)
    (by rw [hNewLCol]) (by rw [hNewRCol]) data.u_frontier data.z_frontier
    (by simpa only [hNewLCol, hNewRCol] using hStrict.le)
  refine ⟨data, ?_, ?_⟩
  · apply hCompare.2.2.mp
    simpa only [hNewLCol, hNewRCol] using hStrict
  · simpa only [hNewLCol, hNewRCol] using hCompare.1

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_nonmarker_split_comparison
