/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighPathDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.HighEventTailSampling
import OmegaY.Expansion.ActualHighFrontierCopy
import OmegaY.Expansion.ActualEffectivePathDepth

/-!
# Actual high-event depth differences along completely copied parent paths

The completed outer execution selects the target event by its exact high
tail sampling. Actual effective-copy execution identifies the starting
target frontier. Source parent closure and copied stored-parent closure
then give paths with the same number of edges. The relative depth balance
is a consequence, with neither a target event nor its frontier supplied.

Both source endpoints must lie strictly right of the bad root. This file
does not handle root-column or fixed-good endpoints, and does not identify
the target event forest with a recovered numerical-parent forest.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- An actual high-event path and its copied path have the same edge count
and hence the same relative depth. Every target event/node below is an
output of the construction theorem. -/
structure HighCopiedPathDepth {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (child parent : (Frame.ofMountain p.reduced).Node) (sourceEvent : Nat)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient) where
  source_width : 0 < p.reduced.size
  target_width : 0 < ambient.size
  targetEvent : Nat
  length : Nat
  childNode : (Frame.ofMountain ambient).Node
  parentNode : (Frame.ofMountain ambient).Node
  target_event_start : (Frame.ofMountain ambient).highEventStart p.lastTop.row ≤ targetEvent
  target_event_end : targetEvent ≤ (Frame.ofMountain ambient).lastEvent
  event_row : (Frame.ofMountain ambient).eventCut targetEvent =
    (Frame.ofMountain p.reduced).eventCut sourceEvent
  event_index : (Frame.ofMountain p.reduced).highEventStart p.lastTop.row +
      (targetEvent - (Frame.ofMountain ambient).highEventStart p.lastTop.row) = sourceEvent
  child_reference : Frame.ref childNode = childCopy.outputRef
  child_cell : (Frame.ofMountain ambient).cell childNode = childCopy.read.outputCell
  parent_reference : Frame.ref parentNode = parentCopy.outputRef
  parent_cell : (Frame.ofMountain ambient).cell parentNode = parentCopy.read.outputCell
  child_frontier : eventFrontier s.ambient_valid.toOrdered targetEvent childNode.1 = childNode
  parent_frontier : eventFrontier s.ambient_valid.toOrdered targetEvent parentNode.1 = parentNode
  source_parent_frontier :
    eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent parent.1 = parent
  source_steps : Forests.ParentSteps
    (eventParentMap (build_normal_of_success p.reduced_build).toOrdered source_width
      (p.reduced.size - 1) sourceEvent) child.1.val parent.1.val length
  target_steps : Forests.ParentSteps
    (eventParentMap s.ambient_valid.toOrdered target_width (ambient.size - 1) targetEvent)
      childNode.1.val parentNode.1.val length
  source_depth : parentDepth
      (eventParentMap (build_normal_of_success p.reduced_build).toOrdered source_width
        (p.reduced.size - 1) sourceEvent) child.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered source_width
      (p.reduced.size - 1) sourceEvent) parent.1.val + length
  target_depth : parentDepth
      (eventParentMap s.ambient_valid.toOrdered target_width (ambient.size - 1) targetEvent) childNode.1.val =
    parentDepth (eventParentMap s.ambient_valid.toOrdered target_width (ambient.size - 1) targetEvent)
      parentNode.1.val + length
  depth_balance :
    parentDepth (eventParentMap s.ambient_valid.toOrdered target_width (ambient.size - 1) targetEvent)
        childNode.1.val +
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered source_width
        (p.reduced.size - 1) sourceEvent) parent.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered source_width
        (p.reduced.size - 1) sourceEvent) child.1.val +
      parentDepth (eventParentMap s.ambient_valid.toOrdered target_width (ambient.size - 1) targetEvent)
        parentNode.1.val
  depth_difference :
    parentDepth (eventParentMap s.ambient_valid.toOrdered target_width (ambient.size - 1) targetEvent)
        childNode.1.val -
      parentDepth (eventParentMap s.ambient_valid.toOrdered target_width (ambient.size - 1) targetEvent)
        parentNode.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered source_width
        (p.reduced.size - 1) sourceEvent) child.1.val -
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered source_width
        (p.reduced.size - 1) sourceEvent) parent.1.val

/-- Completely copied source paths at high events automatically occur at
the corresponding actual target event, with equal source/target edge counts
and relative depths. The actual outer result supplies raw geometry as well
as the high sampling; no incoming geometric or target-frontier hypothesis
is needed. -/
theorem DynamicBlockState.actual_high_path_depth
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient) (hLast : 1 < last)
    (hAmbientRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok ambient)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child parent)
    (hRight : p.root.column < parent.1.val)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    Nonempty (HighCopiedPathDepth s child parent sourceEvent childCopy parentCopy) := by
  obtain ⟨targetEvent, hStart, hEnd, hSample, hEventRow⟩ :=
    p.blocks_high_event_correspondence hLast hAmbientRun hSourceEvent hHigh
  obtain ⟨childNode, hChildRef, hChildCell, hChildAt⟩ :=
    childCopy.frontierAt_high hLast s.ambient_valid hHigh hSourceFront
  obtain ⟨parentNode, hParentRef, hParentCell⟩ := Canonical.frame_node_of_cellAt parentCopy.output_read
  have hTargetFront : eventFrontier s.ambient_valid.toOrdered targetEvent childNode.1 = childNode := by
    unfold eventFrontier
    simpa only [hEventRow] using hChildAt
  have hSourceWidth : 0 < p.reduced.size := (Nat.zero_le child.1.val).trans_lt child.1.isLt
  have hTargetWidth : 0 < ambient.size := (Nat.zero_le childNode.1.val).trans_lt childNode.1.isLt
  have hSourceSize : p.reduced.size - 1 < p.reduced.size := by omega
  have hTargetSize : ambient.size - 1 < ambient.size := by omega
  have hSourceBound : child.1.val ≤ p.reduced.size - 1 := by
    have hc : child.1.val < p.reduced.size := child.1.isLt
    omega
  have hTargetBound : childNode.1.val ≤ ambient.size - 1 := by
    have hc : childNode.1.val < ambient.size := childNode.1.isLt
    omega
  have hRaw := (p.blocks_raw_geometry_of_run hLast hAmbientRun).rawRowGeometry
  have hFather := (p.blocks_raw_father_bound_of_run hLast hAmbientRun).rawFatherUpperBound
  obtain ⟨length, hSourceSteps, hTargetSteps, hSourceParentFront, hTargetParentFront⟩ :=
    s.recorded_effective_path_frontier_steps history hLast hRaw hFather hSourceWidth hTargetWidth
      path hRight child.1.isLt childCopy parentCopy hChildRef hParentRef
        hSourceFront hTargetFront hSourceBound hTargetBound
  have hSourceDepth : parentDepth
      (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) child.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) parent.1.val + length := hSourceSteps.depth
    (eventParentMap_leftward (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth hSourceSize sourceEvent)
  have hTargetDepth : parentDepth
      (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent) childNode.1.val =
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        parentNode.1.val + length := hTargetSteps.depth
    (eventParentMap_leftward s.ambient_valid.toOrdered hTargetWidth hTargetSize targetEvent)
  have hEventIndex : (Frame.ofMountain p.reduced).highEventStart p.lastTop.row +
      (targetEvent - (Frame.ofMountain ambient).highEventStart p.lastTop.row) = sourceEvent := hSample
  exact ⟨{
    source_width := hSourceWidth
    target_width := hTargetWidth
    targetEvent := targetEvent
    length := length
    childNode := childNode
    parentNode := parentNode
    target_event_start := hStart
    target_event_end := hEnd
    event_row := hEventRow
    event_index := hEventIndex
    child_reference := hChildRef
    child_cell := hChildCell
    parent_reference := hParentRef
    parent_cell := hParentCell
    child_frontier := hTargetFront
    parent_frontier := hTargetParentFront
    source_parent_frontier := hSourceParentFront
    source_steps := hSourceSteps
    target_steps := hTargetSteps
    source_depth := hSourceDepth
    target_depth := hTargetDepth
    depth_balance := by rw [hSourceDepth, hTargetDepth]; omega
    depth_difference := by rw [hSourceDepth, hTargetDepth]; omega }⟩

/-- The endpoint occurrences themselves can also be recovered from the
actual completed history. Only the genuine source path/frontier and outer
execution remain as inputs. -/
theorem DynamicBlockState.actual_high_path_depth_exists
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient) (hLast : 1 < last)
    (hAmbientRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok ambient)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child parent)
    (hRight : p.root.column < parent.1.val)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child ambient)
      (parentCopy : EffectiveCopyOccurrence p block start references parent ambient),
      Nonempty (HighCopiedPathDepth s child parent sourceEvent childCopy parentCopy) := by
  have hChildRight : p.root.column < child.1.val :=
    hRight.trans_le (path.column_le (build_normal_of_success p.reduced_build).toOrdered)
  obtain ⟨childCopy⟩ := s.prior_effective_occurrence history hLast hChildRight child.1.isLt
  obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hRight parent.1.isLt
  exact ⟨childCopy, parentCopy, s.actual_high_path_depth history hLast hAmbientRun
    path hRight childCopy parentCopy hSourceEvent hHigh hSourceFront⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_high_path_depth
#print axioms OmegaY.Expansion.DynamicBlockState.actual_high_path_depth_exists
