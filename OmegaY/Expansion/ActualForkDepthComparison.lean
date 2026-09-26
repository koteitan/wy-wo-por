/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualForkDepthComparison.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectivePathDepth
import OmegaY.Expansion.ActualSourceRootIndicators
import OmegaY.Expansion.CanonicalEventProjection

/-!
# Depth comparison at actual paired frontiers with a shared copied ancestor

The two current source parents need not agree. Two genuine source paths
to a common ancestor strictly right of the root give the same relative
depth difference after copying, whenever the two effective nodes are
actual frontiers of one target event. Recorded execution supplies all
target path edges; no output numerical normality is assumed.

At a first source depth difference, the actual source's one previous
common-parent condition constructs the second path to the shallower
node's parent. The common target event remains an explicit interface for
the separate event-synchronization argument.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem DynamicBlockState.recorded_fork_depth_comparison
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {left right ancestor : (Frame.ofMountain p.reduced).Node}
    (leftPath : ParentPath (Frame.ofMountain p.reduced) left ancestor)
    (rightPath : ParentPath (Frame.ofMountain p.reduced) right ancestor)
    (hAncestorRight : p.root.column < ancestor.1.val)
    (hLeftBefore : left.1.val < next) (hRightBefore : right.1.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references left ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references right ambient)
    {leftNode rightNode : (Frame.ofMountain ambient).Node}
    (hLeftRef : Frame.ref leftNode = leftCopy.outputRef)
    (hRightRef : Frame.ref rightNode = rightCopy.outputRef)
    {sourceEvent targetEvent : Nat}
    (hSourceLeft : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent left.1 = left)
    (hSourceRight : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right.1 = right)
    (hTargetLeft : eventFrontier s.ambient_valid.toOrdered targetEvent leftNode.1 = leftNode)
    (hTargetRight : eventFrontier s.ambient_valid.toOrdered targetEvent rightNode.1 = rightNode) :
    let sourceMap := eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth (p.reduced.size - 1) sourceEvent
    let targetMap := eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent
    parentDepth targetMap leftNode.1.val + parentDepth sourceMap right.1.val =
      parentDepth sourceMap left.1.val + parentDepth targetMap rightNode.1.val ∧
    (parentDepth sourceMap left.1.val ≤ parentDepth sourceMap right.1.val ↔
      parentDepth targetMap leftNode.1.val ≤ parentDepth targetMap rightNode.1.val) ∧
    (parentDepth sourceMap left.1.val < parentDepth sourceMap right.1.val ↔
      parentDepth targetMap leftNode.1.val < parentDepth targetMap rightNode.1.val) ∧
    (parentDepth sourceMap left.1.val = parentDepth sourceMap right.1.val ↔
      parentDepth targetMap leftNode.1.val = parentDepth targetMap rightNode.1.val) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hAncestorBefore : ancestor.1.val < next := (leftPath.column_le hNormal.toOrdered).trans_lt hLeftBefore
  obtain ⟨ancestorCopy⟩ := s.prior_effective_occurrence history hLast hAncestorRight hAncestorBefore
  obtain ⟨ancestorNode, hAncestorRef, _⟩ := Canonical.frame_node_of_cellAt ancestorCopy.output_read
  have hSourceSize : p.reduced.size - 1 < p.reduced.size := by omega
  have hTargetSize : ambient.size - 1 < ambient.size := by omega
  have hLeftBound : left.1.val ≤ p.reduced.size - 1 := by
    have hc : left.1.val < p.reduced.size := left.1.isLt; omega
  have hRightBound : right.1.val ≤ p.reduced.size - 1 := by
    have hc : right.1.val < p.reduced.size := right.1.isLt; omega
  have hTargetLeftBound : leftNode.1.val ≤ ambient.size - 1 := by
    have hc : leftNode.1.val < ambient.size := leftNode.1.isLt; omega
  have hTargetRightBound : rightNode.1.val ≤ ambient.size - 1 := by
    have hc : rightNode.1.val < ambient.size := rightNode.1.isLt; omega
  have hLeft := s.recorded_effective_path_depth_balance history hLast hStartRun
    hSourceWidth hTargetWidth hSourceSize hTargetSize leftPath hAncestorRight hLeftBefore
      leftCopy ancestorCopy hLeftRef hAncestorRef hSourceLeft hTargetLeft hLeftBound hTargetLeftBound
  have hRight := s.recorded_effective_path_depth_balance history hLast hStartRun
    hSourceWidth hTargetWidth hSourceSize hTargetSize rightPath hAncestorRight hRightBefore
      rightCopy ancestorCopy hRightRef hAncestorRef hSourceRight hTargetRight hRightBound hTargetRightBound
  dsimp only at hLeft hRight ⊢
  omega

/-- At the first difference the source constructs a common typed ancestor
from its preceding common P and earlier equal depths. Current parents are
allowed to differ. If the shallower source parent is copied, the target
depth difference is exact at every actual event containing both copies. -/
theorem DynamicBlockState.first_difference_copied_parent_comparison
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {left right ancestor : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P left = some ancestor)
    (hAncestorRight : p.root.column < ancestor.1.val)
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
    (hOrder : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) sourceEvent) left.1.val ≤
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) sourceEvent) right.1.val) :
    let sourceMap := eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth (p.reduced.size - 1) sourceEvent
    let targetMap := eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent
    parentDepth targetMap leftNode.1.val + parentDepth sourceMap right.1.val =
      parentDepth sourceMap left.1.val + parentDepth targetMap rightNode.1.val ∧
    parentDepth targetMap leftNode.1.val ≤ parentDepth targetMap rightNode.1.val ∧
    (parentDepth sourceMap left.1.val < parentDepth sourceMap right.1.val ↔
      parentDepth targetMap leftNode.1.val < parentDepth targetMap rightNode.1.val) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hBound : p.reduced.size - 1 < p.reduced.size := by omega
  have hLB : left.1.val ≤ p.reduced.size - 1 := by
    have hc : left.1.val < p.reduced.size := left.1.isLt; omega
  have hRB : right.1.val ≤ p.reduced.size - 1 := by
    have hc : right.1.val < p.reduced.size := right.1.isLt; omega
  have hAncestorFront : eventFrontier hNormal.toOrdered sourceEvent ancestor.1 = ancestor :=
    hNormal.eventFrontier_parent sourceEvent left.1 (by simpa only [hSourceLeft] using hParent)
  have hSourceEdge : eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1)
      sourceEvent left.1.val = some ancestor.1.val := by
    rw [hNormal.eventParentMap_at hSourceWidth sourceEvent left.1 hLB, hSourceLeft, hParent]
    rfl
  have hAncestor := build_source_root_ancestor_at_first_difference p.reduced_build hSourceWidth
    hBound left.1 right.1 hLB hRB hCommon hStart hEvent hEarlier hOrder (.single hSourceEdge)
  have rightPath := hNormal.parentPath_of_eventParentMap_ancestor hSourceWidth hBound hRB hAncestor
  rw [eventFrontierNat_eq hNormal.toOrdered hSourceWidth sourceEvent right.1.isLt,
    eventFrontierNat_eq hNormal.toOrdered hSourceWidth sourceEvent ancestor.1.isLt] at rightPath
  have hRightPath : ParentPath (Frame.ofMountain p.reduced) right ancestor := by
    simpa only [hSourceRight, hAncestorFront] using rightPath
  have hCompare := s.recorded_fork_depth_comparison history hLast hStartRun hSourceWidth hTargetWidth
    (.cons hParent (.refl _)) hRightPath hAncestorRight hLeftBefore hRightBefore leftCopy rightCopy
      hLeftRef hRightRef hSourceLeft hSourceRight hTargetLeft hTargetRight
  exact ⟨hCompare.1, hCompare.2.1.mp hOrder, hCompare.2.2.1⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_fork_depth_comparison
#print axioms OmegaY.Expansion.DynamicBlockState.first_difference_copied_parent_comparison
