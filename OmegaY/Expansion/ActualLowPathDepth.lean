/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowPathDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowFrontierCopy
import OmegaY.Expansion.ActualEffectivePathDepth

/-!
# Actual relative depths at a nonmarker's lifted cut

An arbitrary admissible cut determines its actual floor event in the finite
union of rows. All columns have the same frontier at that event and cut.
This does not assume that the lifted cut is itself an actual row.

For an unmarked source-event frontier, actual copy execution identifies the
frontier at its own lifted cut. The copied raw-parent closure then transports
the entire source path through this one target cut, even when the separate
columns have different controlling markers. Source and target paths have
the same edge count and relative depth. This gives neither an absolute-depth
correction nor a common sampling for all source events and columns.
-/

namespace OmegaY.Geometry.Frame

/-- The actual finite floor event of any cut at least one. Its maximality
and every column's frontier correspondence are conclusions of enumeration. -/
theorem event_floor_at_cut {F : Frame} (hF : F.Ordered) {cut : Row}
    (hCut : (1 : Row) ≤ cut) :
    ∃ event, event ≤ F.lastEvent ∧ F.eventCut event ≤ cut ∧
      (∀ row ∈ F.eventCuts, row ≤ cut → row ≤ F.eventCut event) ∧
      ∀ column, eventFrontier hF event column = frontierAt hF cut hCut column := by
  classical
  let eligible := F.eventRows.filter fun row => row ≤ cut
  have hNonempty : eligible.Nonempty :=
    ⟨1, Finset.mem_filter.mpr ⟨F.one_mem_eventRows, hCut⟩⟩
  let chosen := eligible.max' hNonempty
  have hChosenMem : chosen ∈ eligible := Finset.max'_mem eligible hNonempty
  have hChosen := Finset.mem_filter.mp hChosenMem
  obtain ⟨event, hEvent, hRow⟩ := eventCut_of_member (mem_eventCuts.mpr hChosen.1)
  have hBelow : F.eventCut event ≤ cut := hRow ▸ hChosen.2
  have hMax : ∀ row ∈ F.eventCuts, row ≤ cut → row ≤ F.eventCut event := by
    intro row hMem hLe
    rw [hRow]
    exact Finset.le_max' eligible row (Finset.mem_filter.mpr ⟨mem_eventCuts.mp hMem, hLe⟩)
  refine ⟨event, hEvent, hBelow, hMax, ?_⟩
  intro column
  have hSpec := frontierAt_spec hF hCut column
  apply frontierAt_eq_of_upper_barrier hF (F.eventCut_one_le event)
    (node := frontierAt hF cut hCut column)
  · exact hMax _ (real_height_mem_eventCuts hF hSpec.2.1) hSpec.2.2.1
  · intro upper hUpper
    exact hBelow.trans_lt (hSpec.2.2.2.2 upper hUpper)

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- Relative-depth data at an actual floor event of the child's own lifted
cut. The two copied endpoints are actual reads, with no numerical-parent
assertion about the target frame. -/
structure LowCopiedPathDepth {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (child parent : (Frame.ofMountain p.reduced).Node) (sourceEvent : Nat)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient) where
  source_width : 0 < p.reduced.size
  target_width : 0 < ambient.size
  targetEvent : Nat
  length : Nat
  childNode : (Frame.ofMountain ambient).Node
  parentNode : (Frame.ofMountain ambient).Node
  source_event_end : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent
  target_event_end : targetEvent ≤ (Frame.ofMountain ambient).lastEvent
  cut_one : (1 : Row) ≤ childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)
  target_event_below : (Frame.ofMountain ambient).eventCut targetEvent ≤
    childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)
  target_event_maximal : ∀ row ∈ (Frame.ofMountain ambient).eventCuts,
    row ≤ childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) →
      row ≤ (Frame.ofMountain ambient).eventCut targetEvent
  all_frontiers_at_cut : ∀ column,
    eventFrontier s.ambient_valid.toOrdered targetEvent column =
      frontierAt s.ambient_valid.toOrdered
        (childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) cut_one column
  child_reference : Frame.ref childNode = childCopy.outputRef
  child_cell : (Frame.ofMountain ambient).cell childNode = childCopy.read.outputCell
  parent_reference : Frame.ref parentNode = parentCopy.outputRef
  parent_cell : (Frame.ofMountain ambient).cell parentNode = parentCopy.read.outputCell
  child_frontier : eventFrontier s.ambient_valid.toOrdered targetEvent childNode.1 = childNode
  parent_frontier : eventFrontier s.ambient_valid.toOrdered targetEvent parentNode.1 = parentNode
  parent_at_cut : frontierAt s.ambient_valid.toOrdered
    (childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) cut_one parentNode.1 = parentNode
  source_parent_frontier :
    eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent parent.1 = parent
  raw_path : RawRefPath ambient childCopy.outputRef parentCopy.outputRef
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

/-- One genuine source frontier and its copied path suffice. The target
event and both target frontiers are derived from actual copying and raw
father closure; independent lifts along the path need not be identified. -/
theorem DynamicBlockState.actual_low_path_depth
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child parent)
    (hRight : p.root.column < parent.1.val) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    (parentCopy : EffectiveCopyOccurrence p block start references parent ambient)
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    Nonempty (LowCopiedPathDepth s child parent sourceEvent childCopy parentCopy) := by
  obtain ⟨hCut, childNode, hChildRef, hChildCell, hChildAt⟩ :=
    childCopy.eventFrontier_own_lift hLast s.ambient_valid hUnmarked hSourceFront
  obtain ⟨targetEvent, hTargetEvent, hFloor, hMax, hFrontiers⟩ :=
    event_floor_at_cut s.ambient_valid.toOrdered hCut
  have hTargetFront : eventFrontier s.ambient_valid.toOrdered targetEvent childNode.1 = childNode :=
    (hFrontiers childNode.1).trans hChildAt
  obtain ⟨parentNode, hParentRef, hParentCell⟩ := Canonical.frame_node_of_cellAt parentCopy.output_read
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
  obtain ⟨hRaw, hFather⟩ := s.raw_invariants_of_start_run history hLast hStartRun
  obtain ⟨length, hSourceSteps, hTargetSteps, hSourceParentFront, hTargetParentFront⟩ :=
    s.recorded_effective_path_frontier_steps history hLast hRaw hFather hSourceWidth hTargetWidth
      path hRight hBefore childCopy parentCopy hChildRef hParentRef
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
  exact ⟨{
    source_width := hSourceWidth
    target_width := hTargetWidth
    targetEvent := targetEvent
    length := length
    childNode := childNode
    parentNode := parentNode
    source_event_end := hSourceEvent
    target_event_end := hTargetEvent
    cut_one := hCut
    target_event_below := hFloor
    target_event_maximal := hMax
    all_frontiers_at_cut := hFrontiers
    child_reference := hChildRef
    child_cell := hChildCell
    parent_reference := hParentRef
    parent_cell := hParentCell
    child_frontier := hTargetFront
    parent_frontier := hTargetParentFront
    parent_at_cut := (hFrontiers parentNode.1).symm.trans hTargetParentFront
    source_parent_frontier := hSourceParentFront
    raw_path := s.recorded_effective_path history hLast path hRight hBefore childCopy parentCopy
    source_steps := hSourceSteps
    target_steps := hTargetSteps
    source_depth := hSourceDepth
    target_depth := hTargetDepth
    depth_balance := by rw [hSourceDepth, hTargetDepth]; omega
    depth_difference := by rw [hSourceDepth, hTargetDepth]; omega }⟩

/-- The caller need not provide either endpoint occurrence: actual history
constructs both and fixes their controlling markers and output reads. -/
theorem DynamicBlockState.actual_low_path_depth_exists
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child parent)
    (hRight : p.root.column < parent.1.val) (hBefore : child.1.val < next)
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child ambient)
      (parentCopy : EffectiveCopyOccurrence p block start references parent ambient),
      Nonempty (LowCopiedPathDepth s child parent sourceEvent childCopy parentCopy) := by
  have hChildRight : p.root.column < child.1.val :=
    hRight.trans_le (path.column_le (build_normal_of_success p.reduced_build).toOrdered)
  have hParentBefore : parent.1.val < next :=
    (path.column_le (build_normal_of_success p.reduced_build).toOrdered).trans_lt hBefore
  obtain ⟨childCopy⟩ := s.prior_effective_occurrence history hLast hChildRight hBefore
  obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hRight hParentBefore
  exact ⟨childCopy, parentCopy, s.actual_low_path_depth history hLast hStartRun path hRight hBefore
    childCopy parentCopy hUnmarked hSourceEvent hSourceFront⟩

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.event_floor_at_cut
#print axioms OmegaY.Expansion.DynamicBlockState.actual_low_path_depth
#print axioms OmegaY.Expansion.DynamicBlockState.actual_low_path_depth_exists
