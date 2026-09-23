/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFirstDifferenceDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualForkDepthComparison
import OmegaY.Expansion.ActualRootForkDepthComparison
import OmegaY.Expansion.ActualBoundaryDepthComparison
import OmegaY.Expansion.ActualSourceFork

/-!
# Strict depth comparison at paired first-difference frontiers

The actual source's previous common parent and intervening equal depths
give the necessary source fork. All possible parents of the shallower
source node are covered: absent, fixed, root-column, or copied. No marker
exclusion and no high-cut restriction is used in the depth comparison.

The two effective occurrences must be actual frontiers of one target
event. Constructing that event, and controlling earlier inserted events,
are separate obligations. This theorem alone is not depth-word transport.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem DynamicBlockState.first_difference_depth_lt_at_frontiers
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {left right : (Frame.ofMountain p.reduced).Node}
    (hLeftBefore : left.1.val < next) (hRightBefore : right.1.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references left ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references right ambient)
    {leftNode rightNode : (Frame.ofMountain ambient).Node}
    (hLeftRef : Frame.ref leftNode = leftCopy.outputRef)
    (hRightRef : Frame.ref rightNode = rightCopy.outputRef)
    {previous sourceEvent targetEvent : Nat}
    (hCommon : (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left.1) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right.1))
    (hStart : previous + 1 ≤ sourceEvent)
    (hEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hEarlier : ∀ event, previous + 1 ≤ event → event < sourceEvent →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) event) left.1.val =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) event) right.1.val)
    (hSourceLeft : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent left.1 = left)
    (hSourceRight : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right.1 = right)
    (hTargetLeft : eventFrontier s.ambient_valid.toOrdered targetEvent leftNode.1 = leftNode)
    (hTargetRight : eventFrontier s.ambient_valid.toOrdered targetEvent rightNode.1 = rightNode)
    (hStrict : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) sourceEvent) left.1.val <
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) sourceEvent) right.1.val) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        leftNode.1.val <
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        rightNode.1.val := by
  cases hParent : (Frame.ofMountain p.reduced).P left with
  | none =>
      exact (s.depth_order_of_terminal_or_fixed_left history hLast hStartRun hSourceWidth hTargetWidth
        leftCopy.state.next_lower hLeftBefore leftCopy hEvent hSourceLeft hLeftRef hTargetLeft
          (.inl hParent) rightCopy.state.next_lower hRightBefore rightCopy hRightRef hSourceRight hTargetRight).2 hStrict
  | some ancestor =>
      by_cases hFixed : ancestor.1.val < p.root.column
      · exact (s.depth_order_of_terminal_or_fixed_left history hLast hStartRun hSourceWidth hTargetWidth
          leftCopy.state.next_lower hLeftBefore leftCopy hEvent hSourceLeft hLeftRef hTargetLeft
            (.inr ⟨ancestor, hParent, hFixed⟩) rightCopy.state.next_lower hRightBefore rightCopy
              hRightRef hSourceRight hTargetRight).2 hStrict
      · obtain ⟨hLeftPath, hRightPath⟩ := build_source_parent_fork_at_first_difference p.reduced_build
          hSourceWidth left.1 right.1 hCommon hStart hEvent hEarlier hStrict.le
            (by simpa only [hSourceLeft] using hParent)
        have leftPath : ParentPath (Frame.ofMountain p.reduced) left ancestor :=
          by simpa only [hSourceLeft] using hLeftPath
        have rightPath : ParentPath (Frame.ofMountain p.reduced) right ancestor :=
          by simpa only [hSourceRight] using hRightPath
        rcases eq_or_lt_of_le (Nat.le_of_not_gt hFixed) with hRoot | hRight
        · exact (s.recorded_root_fork_depth_comparison history hLast hStartRun hSourceWidth hTargetWidth
            leftPath rightPath hRoot.symm leftCopy.state.next_lower rightCopy.state.next_lower
              hLeftBefore hRightBefore leftCopy rightCopy hLeftRef hRightRef hSourceLeft hSourceRight
                hTargetLeft hTargetRight).2.2.1.mp hStrict
        · exact (s.recorded_fork_depth_comparison history hLast hStartRun hSourceWidth hTargetWidth
            leftPath rightPath hRight hLeftBefore hRightBefore leftCopy rightCopy hLeftRef hRightRef
              hSourceLeft hSourceRight hTargetLeft hTargetRight).2.2.1.mp hStrict

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.first_difference_depth_lt_at_frontiers
