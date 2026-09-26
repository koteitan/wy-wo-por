/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualAllSourceDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowCopiedDepth
import OmegaY.Expansion.ActualMarkedFrontierCopy

/-!
# Corrected actual event depths for every copied source frontier

The actual marker successor now supplies the previously missing marked
frontier case. The path, root and fixed-exit constructors below use the
same genuine raw-parent paths and floor-event construction as their
nonmarker predecessors. Their only geometric entrance is the actual
source event frontier, and all target frontiers are derived from execution.

No marker-status restriction remains. The final depth is the source depth
plus a natural correction. This remains a single-source, own-cut result;
shared cuts, value comparison and expansion descent are not asserted here.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- Every source frontier supplies the actual lifted cut and both
endpoints of its copied parent path with equal edge counts. -/
theorem DynamicBlockState.actual_all_source_path_depth
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
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    Nonempty (LowCopiedPathDepth s child parent sourceEvent childCopy parentCopy) := by
  obtain ⟨hCut, childNode, hChildRef, hChildCell, hChildAt⟩ :=
    childCopy.eventFrontier_own_lift_all hLast s.ambient_valid hSourceFront
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

/-- A genuine source edge into the root column constructs its actual
start-boundary endpoint and the uncorrected depth balance. -/
theorem DynamicBlockState.actual_all_source_root_path_depth
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {child lastBad root : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child lastBad)
    (hExit : (Frame.ofMountain p.reduced).P lastBad = some root)
    (hRootColumn : root.1.val = p.root.column) (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    Nonempty (LowRootPathDepth s child lastBad root sourceEvent childCopy) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRight : p.root.column < lastBad.1.val := hRootColumn ▸ P_column_lt hNormal.toOrdered hExit
  have hLastBefore : lastBad.1.val < next := (path.column_le hNormal.toOrdered).trans_lt hBefore
  obtain ⟨lastCopy⟩ := s.prior_effective_occurrence history hLast hRight hLastBefore
  obtain ⟨data⟩ := s.actual_all_source_path_depth history hLast hStartRun path hRight hBefore
    childCopy lastCopy hSourceEvent hSourceFront
  obtain ⟨rootCopy, hEdge⟩ := s.recorded_root_parent_exists history hLast hStartRun hExit
    hRootColumn hLastBefore lastCopy
  obtain ⟨rootNode, hRootRef, hRootCell⟩ := Canonical.frame_node_of_cellAt rootCopy.result_read
  have hRootNodeColumn : rootNode.1.val = start.size - 1 :=
    (congrArg Ref.column hRootRef).trans rootCopy.reference_column
  have hRawEdge : (Frame.ofMountain ambient).rawParent data.parentNode = some rootNode :=
    hEdge.rawParent data.parent_reference hRootRef
  obtain ⟨hRaw, hFather⟩ := s.raw_invariants_of_start_run history hLast hStartRun
  have hRootFront : eventFrontier s.ambient_valid.toOrdered data.targetEvent rootNode.1 = rootNode :=
    eventFrontier_raw_parent_of_bound s.ambient_valid.toOrdered hRaw hFather data.targetEvent
      data.parentNode.1 (by rw [data.parent_frontier]; exact hRawEdge)
  have hSourceRootFront : eventFrontier hNormal.toOrdered sourceEvent root.1 = root :=
    hNormal.eventFrontier_parent sourceEvent lastBad.1
      (by rw [data.source_parent_frontier]; exact hExit)
  have hSourceBound : lastBad.1.val ≤ p.reduced.size - 1 := by
    have hc : lastBad.1.val < p.reduced.size := lastBad.1.isLt
    omega
  have hTargetBound : data.parentNode.1.val ≤ ambient.size - 1 := by
    have hc : data.parentNode.1.val < ambient.size := data.parentNode.1.isLt
    omega
  have hSourceEdge : eventParentMap hNormal.toOrdered data.source_width (p.reduced.size - 1)
      sourceEvent lastBad.1.val = some root.1.val := by
    rw [hNormal.eventParentMap_at data.source_width sourceEvent lastBad.1 hSourceBound,
      data.source_parent_frontier, hExit]
    rfl
  have hTargetEdge : eventParentMap s.ambient_valid.toOrdered data.target_width (ambient.size - 1)
      data.targetEvent data.parentNode.1.val = some (start.size - 1) := by
    rw [eventParentMap_raw_at s.ambient_valid.toOrdered data.target_width data.targetEvent
      data.parentNode.1 hTargetBound, data.parent_frontier, hRawEdge]
    simp only [Option.map_some, hRootNodeColumn]
  have hSourceSteps : Forests.ParentSteps
      (eventParentMap hNormal.toOrdered data.source_width (p.reduced.size - 1) sourceEvent)
      child.1.val root.1.val (data.length + 1) :=
    data.source_steps.trans (.cons hSourceEdge (.nil _))
  have hTargetSteps : Forests.ParentSteps
      (eventParentMap s.ambient_valid.toOrdered data.target_width (ambient.size - 1) data.targetEvent)
      data.childNode.1.val (start.size - 1) (data.length + 1) :=
    data.target_steps.trans (.cons hTargetEdge (.nil _))
  obtain ⟨startEvent, hStartEvent, hStartBelow, hStartMax, hStartFrontiers⟩ :=
    event_floor_at_cut s.start_valid.toOrdered data.cut_one
  obtain ⟨startNode, hStartRef, hStartCell⟩ := Canonical.frame_node_of_cellAt rootCopy.start_read
  have hStartColumn : startNode.1.val = start.size - 1 :=
    (congrArg Ref.column hStartRef).trans rootCopy.reference_column
  have hStartWidth : 0 < start.size := (Nat.zero_le startNode.1.val).trans_lt startNode.1.isLt
  have hStartBound : start.size - 1 < start.size := by omega
  have hStartFront : eventFrontier s.start_valid.toOrdered startEvent startNode.1 = startNode := by
    have hFront : frontierAt s.ambient_valid.toOrdered
        (childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) data.cut_one
        rootNode.1 = rootNode := (data.all_frontiers_at_cut rootNode.1).symm.trans hRootFront
    have hColumns : start[rootNode.1.val]? = ambient[rootNode.1.val]? :=
      (s.start_preserved rootNode.1.val (hRootNodeColumn ▸ hStartBound)).symm
    exact (hStartFrontiers startNode.1).trans (frontierAt_of_same_column
      s.ambient_valid.toOrdered s.start_valid.toOrdered data.cut_one hFront
        (hStartRef.trans hRootRef.symm) hColumns)
  have hBoundaryDepth := s.start_preserved.event_parentDepth_at_common_cut
    s.start_valid.toOrdered s.ambient_valid.toOrdered hStartWidth data.target_width data.cut_one
    hStartFrontiers data.all_frontiers_at_cut hStartBound
  have hSourceSize : p.reduced.size - 1 < p.reduced.size := by have := data.source_width; omega
  have hTargetSize : ambient.size - 1 < ambient.size := by have := data.target_width; omega
  have hSourceDepth : parentDepth (eventParentMap hNormal.toOrdered data.source_width
        (p.reduced.size - 1) sourceEvent) child.1.val =
      parentDepth (eventParentMap hNormal.toOrdered data.source_width
        (p.reduced.size - 1) sourceEvent) root.1.val + (data.length + 1) := hSourceSteps.depth
    (eventParentMap_leftward hNormal.toOrdered data.source_width hSourceSize sourceEvent)
  have hTargetDepth : parentDepth (eventParentMap s.ambient_valid.toOrdered data.target_width
        (ambient.size - 1) data.targetEvent) data.childNode.1.val =
      parentDepth (eventParentMap s.start_valid.toOrdered hStartWidth
        (start.size - 1) startEvent) (start.size - 1) + (data.length + 1) := by
    exact (hTargetSteps.depth (eventParentMap_leftward s.ambient_valid.toOrdered
      data.target_width hTargetSize data.targetEvent)).trans (congrArg (· + (data.length + 1)) hBoundaryDepth)
  exact ⟨{
    lastCopy := lastCopy, copied := data, rootCopy := rootCopy, rootNode := rootNode
    root_reference := hRootRef, root_cell := hRootCell, root_column := hRootNodeColumn
    root_frontier := hRootFront, source_root_frontier := hSourceRootFront
    start_width := hStartWidth, startEvent := startEvent, start_event_end := hStartEvent
    start_event_below := hStartBelow, start_event_maximal := hStartMax
    start_frontiers_at_cut := hStartFrontiers
    startNode := startNode, start_reference := hStartRef, start_cell := hStartCell
    start_column := hStartColumn, start_frontier := hStartFront
    raw_path := data.raw_path.trans (.cons hEdge (.refl _))
    source_steps := hSourceSteps, target_steps := hTargetSteps
    boundary_depth := hBoundaryDepth, source_depth := hSourceDepth, target_depth := hTargetDepth
    depth_balance := by rw [hTargetDepth, hSourceDepth]; omega }⟩

private theorem all_source_path_eq_or_last_edge {F : Frame} {child root : F.Node}
    (path : ParentPath F child root) :
    child = root ∨ ∃ lastBad, ParentPath F child lastBad ∧ F.P lastBad = some root := by
  induction path with
  | refl _ => exact Or.inl rfl
  | @cons child middle root hParent rest ih =>
      rcases ih with he | ⟨lastBad, hPath, hLast⟩
      · subst middle
        exact Or.inr ⟨child, .refl _, hParent⟩
      · exact Or.inr ⟨lastBad, .cons hParent hPath, hLast⟩

/-- A complete source path into the root column determines its last edge
and hence the low-root balance, without supplying that edge separately. -/
theorem DynamicBlockState.actual_all_source_root_path_depth_of_path
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {child root : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child root)
    (hRootColumn : root.1.val = p.root.column) (hChildRight : p.root.column < child.1.val)
    (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    ∃ lastBad, ParentPath (Frame.ofMountain p.reduced) child lastBad ∧
      (Frame.ofMountain p.reduced).P lastBad = some root ∧
      Nonempty (LowRootPathDepth s child lastBad root sourceEvent childCopy) := by
  rcases all_source_path_eq_or_last_edge path with he | ⟨lastBad, hPrefix, hExit⟩
  · have hc := congrArg (fun node => node.1.val) he
    omega
  · exact ⟨lastBad, hPrefix, hExit, s.actual_all_source_root_path_depth history hLast hStartRun
      hPrefix hExit hRootColumn hBefore childCopy hSourceEvent hSourceFront⟩

/-- A fixed-prefix exit has zero absolute-depth correction at the
source occurrence's actual lifted cut, without a marker-status test. -/
theorem DynamicBlockState.actual_all_source_fixed_path_depth
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {child lastBad fixedParent : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child lastBad)
    (hExit : (Frame.ofMountain p.reduced).P lastBad = some fixedParent)
    (hRight : p.root.column < lastBad.1.val) (hFixed : fixedParent.1.val < p.root.column)
    (hBefore : child.1.val < next)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    Nonempty (LowFixedPathDepth s child lastBad fixedParent sourceEvent childCopy) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hLastBefore : lastBad.1.val < next := (path.column_le hNormal.toOrdered).trans_lt hBefore
  obtain ⟨lastCopy⟩ := s.prior_effective_occurrence history hLast hRight hLastBefore
  obtain ⟨data⟩ := s.actual_all_source_path_depth history hLast hStartRun path hRight hBefore
    childCopy lastCopy hSourceEvent hSourceFront
  obtain ⟨hEdge, _⟩ := s.recorded_fixed_parent history hLast hExit hRight hLastBefore hFixed lastCopy
  let fixedNode := s.base_ambient.mapNode fixedParent
  have hFixedRef : Frame.ref fixedNode = Frame.ref fixedParent := s.base_ambient.mapNode_ref fixedParent
  have hFixedCell : (Frame.ofMountain ambient).cell fixedNode =
      (Frame.ofMountain p.reduced).cell fixedParent := s.base_ambient.mapNode_cell fixedParent
  have hFixedColumn : fixedNode.1.val = fixedParent.1.val := s.base_ambient.mapNode_column fixedParent
  have hRawEdge : (Frame.ofMountain ambient).rawParent data.parentNode = some fixedNode :=
    hEdge.rawParent data.parent_reference hFixedRef
  obtain ⟨hRaw, hFather⟩ := s.raw_invariants_of_start_run history hLast hStartRun
  have hFixedFront : eventFrontier s.ambient_valid.toOrdered data.targetEvent fixedNode.1 = fixedNode :=
    eventFrontier_raw_parent_of_bound s.ambient_valid.toOrdered hRaw hFather data.targetEvent
      data.parentNode.1 (by rw [data.parent_frontier]; exact hRawEdge)
  have hSourceFixedFront : eventFrontier hNormal.toOrdered sourceEvent fixedParent.1 = fixedParent :=
    hNormal.eventFrontier_parent sourceEvent lastBad.1
      (by rw [data.source_parent_frontier]; exact hExit)
  have hSourceBound : lastBad.1.val ≤ p.reduced.size - 1 := by
    have hc : lastBad.1.val < p.reduced.size := lastBad.1.isLt
    omega
  have hTargetBound : data.parentNode.1.val ≤ ambient.size - 1 := by
    have hc : data.parentNode.1.val < ambient.size := data.parentNode.1.isLt
    omega
  have hSourceEdge : eventParentMap hNormal.toOrdered data.source_width (p.reduced.size - 1)
      sourceEvent lastBad.1.val = some fixedParent.1.val := by
    rw [hNormal.eventParentMap_at data.source_width sourceEvent lastBad.1 hSourceBound,
      data.source_parent_frontier, hExit]
    rfl
  have hTargetEdge : eventParentMap s.ambient_valid.toOrdered data.target_width (ambient.size - 1)
      data.targetEvent data.parentNode.1.val = some fixedParent.1.val := by
    rw [eventParentMap_raw_at s.ambient_valid.toOrdered data.target_width data.targetEvent
      data.parentNode.1 hTargetBound, data.parent_frontier, hRawEdge]
    simp only [Option.map_some, hFixedColumn]
  have hSourceSteps : Forests.ParentSteps
      (eventParentMap hNormal.toOrdered data.source_width (p.reduced.size - 1) sourceEvent)
      child.1.val fixedParent.1.val (data.length + 1) :=
    data.source_steps.trans (.cons hSourceEdge (.nil _))
  have hTargetSteps : Forests.ParentSteps
      (eventParentMap s.ambient_valid.toOrdered data.target_width (ambient.size - 1) data.targetEvent)
      data.childNode.1.val fixedParent.1.val (data.length + 1) :=
    data.target_steps.trans (.cons hTargetEdge (.nil _))
  have hFixedDepth := s.base_ambient.event_parentDepth_of_common_frontier hNormal
    s.ambient_valid.toOrdered hRaw hFather data.source_width data.target_width
      hSourceFixedFront hFixedFront
  have hSourceSize : p.reduced.size - 1 < p.reduced.size := by have := data.source_width; omega
  have hTargetSize : ambient.size - 1 < ambient.size := by have := data.target_width; omega
  have hSourceDepth : parentDepth
      (eventParentMap hNormal.toOrdered data.source_width (p.reduced.size - 1) sourceEvent) child.1.val =
      parentDepth (eventParentMap hNormal.toOrdered data.source_width (p.reduced.size - 1) sourceEvent)
        fixedParent.1.val + (data.length + 1) :=
    hSourceSteps.depth (eventParentMap_leftward hNormal.toOrdered data.source_width hSourceSize sourceEvent)
  have hTargetDepth : parentDepth
      (eventParentMap s.ambient_valid.toOrdered data.target_width (ambient.size - 1) data.targetEvent)
        data.childNode.1.val =
      parentDepth (eventParentMap s.ambient_valid.toOrdered data.target_width (ambient.size - 1) data.targetEvent)
        fixedParent.1.val + (data.length + 1) :=
    hTargetSteps.depth (eventParentMap_leftward s.ambient_valid.toOrdered data.target_width hTargetSize data.targetEvent)
  exact ⟨{
    lastCopy := lastCopy, copied := data, fixedNode := fixedNode
    fixed_reference := hFixedRef, fixed_cell := hFixedCell
    fixed_frontier := hFixedFront, source_fixed_frontier := hSourceFixedFront
    raw_path := data.raw_path.trans (.cons hEdge (.refl _))
    source_steps := hSourceSteps, target_steps := hTargetSteps
    fixed_depth := hFixedDepth
    absolute_depth := by rw [hTargetDepth, hSourceDepth, hFixedDepth] }⟩

/-- Every actual copied source frontier has its source absolute depth
plus a natural correction. Parent-path exit selection is internal. -/
theorem DynamicBlockState.actual_all_source_copied_depth
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {source : (Frame.ofMountain p.reduced).Node}
    (hRight : p.root.column < source.1.val) (hBefore : source.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source ambient)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent source.1 = source) :
    Nonempty (LowCopiedDepth s source sourceEvent copy) := by
  have hNormal := build_normal_of_success p.reduced_build
  rcases Frame.parent_path_exit hNormal.toOrdered hRight with
    ⟨terminal, path, hTerminalRight, hNone⟩ |
    ⟨root, path, hRootColumn⟩ | ⟨lastBad, fixed, path, hBadRight, hExit, hFixed⟩
  · have hTerminalBefore : terminal.1.val < next :=
      (path.column_le hNormal.toOrdered).trans_lt hBefore
    obtain ⟨terminalCopy⟩ := s.prior_effective_occurrence history hLast hTerminalRight hTerminalBefore
    obtain ⟨packet⟩ := s.actual_all_source_path_depth history hLast hStartRun path hTerminalRight hBefore
      copy terminalCopy hSourceEvent hSourceFront
    exact ⟨packet.toCorrected 0 (by simpa only [Nat.add_zero] using
      (packet.terminal_depths hLast hNone).2.2)⟩
  · obtain ⟨lastBad, _, _, ⟨packet⟩⟩ := s.actual_all_source_root_path_depth_of_path history hLast
      hStartRun path hRootColumn hRight hBefore copy hSourceEvent hSourceFront
    obtain ⟨increment, _, hDepth⟩ := packet.correction hLast hStartRun
    exact ⟨packet.copied.toCorrected increment hDepth⟩
  · obtain ⟨packet⟩ := s.actual_all_source_fixed_path_depth history hLast hStartRun path hExit
      hBadRight hFixed hBefore copy hSourceEvent hSourceFront
    exact ⟨packet.copied.toCorrected 0 (by simpa only [Nat.add_zero] using packet.absolute_depth)⟩


/-- Actual recorded execution supplies the occurrence as well as its
corrected depth packet; no target read or frontier is an external input. -/
theorem DynamicBlockState.actual_all_source_copied_depth_exists
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {source : (Frame.ofMountain p.reduced).Node}
    (hRight : p.root.column < source.1.val) (hBefore : source.1.val < next)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent source.1 = source) :
    ∃ copy : EffectiveCopyOccurrence p block start references source ambient,
      Nonempty (LowCopiedDepth s source sourceEvent copy) := by
  obtain ⟨copy⟩ := s.prior_effective_occurrence history hLast hRight hBefore
  exact ⟨copy, s.actual_all_source_copied_depth history hLast hStartRun hRight hBefore
    copy hSourceEvent hSourceFront⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_all_source_path_depth
#print axioms OmegaY.Expansion.DynamicBlockState.actual_all_source_root_path_depth
#print axioms OmegaY.Expansion.DynamicBlockState.actual_all_source_root_path_depth_of_path
#print axioms OmegaY.Expansion.DynamicBlockState.actual_all_source_fixed_path_depth
#print axioms OmegaY.Expansion.DynamicBlockState.actual_all_source_copied_depth
#print axioms OmegaY.Expansion.DynamicBlockState.actual_all_source_copied_depth_exists
