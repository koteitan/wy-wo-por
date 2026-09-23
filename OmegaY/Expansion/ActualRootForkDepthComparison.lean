/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootForkDepthComparison.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectivePathDepth
import OmegaY.Expansion.ActualRecordedRootParents

/-!
# Exact depth differences through one actual root endpoint

Source paths into the same root-column node have the same relative depth
differences after copying. Recorded execution supplies every copied edge,
including the final edge to the selected or high-tail root endpoint.
Endpoint uniqueness aligns these last edges at their common block start.

The source and target starting nodes are actual event frontiers. The shared
target event is an explicit interface; this module does not construct a
global sampling, assume output numerical normality, or exclude markers.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

private theorem root_path_last_edge {F : Frame} {child root : F.Node}
    (path : ParentPath F child root) :
    child = root ∨ ∃ lastBad, ParentPath F child lastBad ∧ F.P lastBad = some root := by
  induction path with
  | refl _ => exact Or.inl rfl
  | @cons child middle root hParent rest ih =>
    rcases ih with he | ⟨lastBad, hPath, hLast⟩
    · subst middle
      exact Or.inr ⟨child, .refl _, hParent⟩
    · exact Or.inr ⟨lastBad, .cons hParent hPath, hLast⟩

/-- The actual root endpoint may be chosen independently: its uniqueness
at the common start aligns the recorded last edge. The complete source
and target paths have the same edge count at the given frontier events. -/
theorem DynamicBlockState.recorded_root_path_depth_balance
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {child root : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child root)
    (hRootColumn : root.1.val = p.root.column) (hChildRight : p.root.column < child.1.val)
    (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (rootCopy : EffectiveRootEndpoint p start references root ambient)
    {childNode rootNode : (Frame.ofMountain ambient).Node}
    (hChildRef : Frame.ref childNode = childCopy.outputRef)
    (hRootRef : Frame.ref rootNode = rootCopy.reference)
    {sourceEvent targetEvent : Nat}
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child)
    (hTargetFront : eventFrontier s.ambient_valid.toOrdered targetEvent childNode.1 = childNode) :
    let sourceMap := eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth (p.reduced.size - 1) sourceEvent
    let targetMap := eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent
    parentDepth targetMap childNode.1.val + parentDepth sourceMap root.1.val =
      parentDepth sourceMap child.1.val + parentDepth targetMap rootNode.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  rcases root_path_last_edge path with he | ⟨lastBad, hPath, hExit⟩
  · have hc := congrArg (fun node => node.1.val) he
    omega
  · have hLastRight : p.root.column < lastBad.1.val := hRootColumn ▸ P_column_lt hNormal.toOrdered hExit
    have hLastBefore := (hPath.column_le hNormal.toOrdered).trans_lt hBefore
    obtain ⟨lastCopy⟩ := s.prior_effective_occurrence history hLast hLastRight hLastBefore
    obtain ⟨lastNode, hLastRef, _⟩ := Canonical.frame_node_of_cellAt lastCopy.output_read
    obtain ⟨hRaw, hFather⟩ := s.raw_invariants_of_start_run history hLast hStartRun
    have hSourceBound : child.1.val ≤ p.reduced.size - 1 := by
      have hc : child.1.val < p.reduced.size := child.1.isLt
      omega
    have hTargetBound : childNode.1.val ≤ ambient.size - 1 := by
      have hc : childNode.1.val < ambient.size := childNode.1.isLt
      omega
    obtain ⟨length, hSourceSteps, hTargetSteps, hSourceLast, hTargetLast⟩ :=
      s.recorded_effective_path_frontier_steps history hLast hRaw hFather hSourceWidth hTargetWidth
        hPath hLastRight hBefore childCopy lastCopy hChildRef hLastRef
          hSourceFront hTargetFront hSourceBound hTargetBound
    have hRootEdge := s.recorded_root_parent history hLast hStartRun hExit hRootColumn hLastBefore
      lastCopy rootCopy
    have hRawEdge : (Frame.ofMountain ambient).rawParent lastNode = some rootNode :=
      hRootEdge.rawParent hLastRef hRootRef
    have hLastSourceBound : lastBad.1.val ≤ p.reduced.size - 1 := by
      have hc : lastBad.1.val < p.reduced.size := lastBad.1.isLt
      omega
    have hLastTargetBound : lastNode.1.val ≤ ambient.size - 1 := by
      have hc : lastNode.1.val < ambient.size := lastNode.1.isLt
      omega
    have hSourceEdge : eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1)
        sourceEvent lastBad.1.val = some root.1.val := by
      rw [hNormal.eventParentMap_at hSourceWidth sourceEvent lastBad.1 hLastSourceBound,
        hSourceLast, hExit]
      rfl
    have hTargetEdge : eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1)
        targetEvent lastNode.1.val = some rootNode.1.val := by
      rw [eventParentMap_raw_at s.ambient_valid.toOrdered hTargetWidth targetEvent lastNode.1
        hLastTargetBound, hTargetLast, hRawEdge]
      rfl
    have hSourceAll : Forests.ParentSteps
        (eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1) sourceEvent)
        child.1.val root.1.val (length + 1) :=
      hSourceSteps.trans (.cons hSourceEdge (.nil _))
    have hTargetAll : Forests.ParentSteps
        (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        childNode.1.val rootNode.1.val (length + 1) :=
      hTargetSteps.trans (.cons hTargetEdge (.nil _))
    have hSourceSize : p.reduced.size - 1 < p.reduced.size := by omega
    have hTargetSize : ambient.size - 1 < ambient.size := by omega
    have hSourceDepth : parentDepth
        (eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1) sourceEvent) child.1.val =
      parentDepth (eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1) sourceEvent)
        root.1.val + (length + 1) := hSourceAll.depth
          (eventParentMap_leftward hNormal.toOrdered hSourceWidth hSourceSize sourceEvent)
    have hTargetDepth : parentDepth
        (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent) childNode.1.val =
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        rootNode.1.val + (length + 1) := hTargetAll.depth
          (eventParentMap_leftward s.ambient_valid.toOrdered hTargetWidth hTargetSize targetEvent)
    dsimp only at hSourceDepth hTargetDepth ⊢
    omega

/-- Two actual source paths into one root-column node preserve their
precise relative depths at any one target event containing both effective
copies. Neither the root correction nor an event-height lower bound is a
premise. All marker statuses and all root endpoint cases are included. -/
theorem DynamicBlockState.recorded_root_fork_depth_comparison
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
    (hRootColumn : ancestor.1.val = p.root.column)
    (hLeftRight : p.root.column < left.1.val) (hRightRight : p.root.column < right.1.val)
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
  rcases root_path_last_edge leftPath with he | ⟨lastBad, hPath, hExit⟩
  · have hc := congrArg (fun node => node.1.val) he
    omega
  · have hLastRight : p.root.column < lastBad.1.val := hRootColumn ▸ P_column_lt hNormal.toOrdered hExit
    have hLastBefore := (hPath.column_le hNormal.toOrdered).trans_lt hLeftBefore
    obtain ⟨lastCopy⟩ := s.prior_effective_occurrence history hLast hLastRight hLastBefore
    obtain ⟨rootCopy, _⟩ := s.recorded_root_parent_exists history hLast hStartRun hExit hRootColumn
      hLastBefore lastCopy
    obtain ⟨rootNode, hRootRef, _⟩ := Canonical.frame_node_of_cellAt rootCopy.result_read
    have hLeft := s.recorded_root_path_depth_balance history hLast hStartRun hSourceWidth hTargetWidth
      leftPath hRootColumn hLeftRight hLeftBefore leftCopy rootCopy hLeftRef hRootRef hSourceLeft hTargetLeft
    have hRight := s.recorded_root_path_depth_balance history hLast hStartRun hSourceWidth hTargetWidth
      rightPath hRootColumn hRightRight hRightBefore rightCopy rootCopy hRightRef hRootRef hSourceRight hTargetRight
    dsimp only at hLeft hRight ⊢
    omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_root_path_depth_balance
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_root_fork_depth_comparison
