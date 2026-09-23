/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighRootPathDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighPathDepth
import OmegaY.Expansion.ActualHighRootDepth
import OmegaY.Expansion.RecordedRootPaths

/-!
# Absolute high-event depth for source paths entering the root column

The completely copied prefix has the same edge count as its source. The
last real copied edge ends at the block-start boundary. Raw parent closure
identifies that endpoint as the actual high-cut frontier, including both
selected references and high-tail occurrences. The executed start prefix
supplies its root depth, and complete-column preservation carries that
depth into the finished block. No endpoint-depth or target-frontier
agreement is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem EffectiveRootEndpoint.reference_column
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references source result) :
    endpoint.reference.column = start.size - 1 := by
  cases endpoint with
  | selected copy => exact copy.reference_column
  | highTail copy => exact copy.reference_column

theorem EffectiveRootEndpoint.start_read
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references source result) :
    Canonical.cellAt start endpoint.reference = .ok endpoint.target := by
  cases endpoint with
  | selected copy => exact copy.start_read
  | highTail copy => exact copy.start_read

structure HighRootPathDepth {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (child lastBad root : (Frame.ofMountain p.reduced).Node) (sourceEvent : Nat)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient) where
  lastCopy : EffectiveCopyOccurrence p block start references lastBad ambient
  copied : HighCopiedPathDepth s child lastBad sourceEvent childCopy lastCopy
  rootCopy : EffectiveRootEndpoint p start references root ambient
  rootNode : (Frame.ofMountain ambient).Node
  root_reference : Frame.ref rootNode = rootCopy.reference
  root_cell : (Frame.ofMountain ambient).cell rootNode = rootCopy.target
  root_column : rootNode.1.val = start.size - 1
  root_frontier : eventFrontier s.ambient_valid.toOrdered copied.targetEvent rootNode.1 = rootNode
  source_root_frontier : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
    sourceEvent root.1 = root
  start_width : 0 < start.size
  startEvent : Nat
  start_event_row : (Frame.ofMountain start).eventCut startEvent =
    (Frame.ofMountain p.reduced).eventCut sourceEvent
  startNode : (Frame.ofMountain start).Node
  start_reference : Frame.ref startNode = rootCopy.reference
  start_cell : (Frame.ofMountain start).cell startNode = rootCopy.target
  start_frontier : eventFrontier s.start_valid.toOrdered startEvent startNode.1 = startNode
  raw_path : RawRefPath ambient childCopy.outputRef rootCopy.reference
  source_steps : Forests.ParentSteps
    (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
      (p.reduced.size - 1) sourceEvent) child.1.val root.1.val (copied.length + 1)
  target_steps : Forests.ParentSteps
    (eventParentMap s.ambient_valid.toOrdered copied.target_width (ambient.size - 1) copied.targetEvent)
      copied.childNode.1.val (start.size - 1) (copied.length + 1)
  root_depth :
    parentDepth (eventParentMap s.ambient_valid.toOrdered copied.target_width
      (ambient.size - 1) copied.targetEvent) (start.size - 1) =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
      (p.reduced.size - 1) sourceEvent) root.1.val
  absolute_depth :
    parentDepth (eventParentMap s.ambient_valid.toOrdered copied.target_width
      (ambient.size - 1) copied.targetEvent) copied.childNode.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
      (p.reduced.size - 1) sourceEvent) child.1.val

/-- A copied high-frontier path followed by its actual source edge into
the root column has unchanged absolute depth. Both the finished block and
its starting boundary are genuine outer-loop outputs. -/
theorem DynamicBlockState.actual_high_root_path_depth
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies startCopies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hAmbientRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok ambient)
    {child lastBad root : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child lastBad)
    (hExit : (Frame.ofMountain p.reduced).P lastBad = some root)
    (hRootColumn : root.1.val = p.root.column)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    Nonempty (HighRootPathDepth s child lastBad root sourceEvent childCopy) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRight : p.root.column < lastBad.1.val :=
    hRootColumn ▸ P_column_lt hNormal.toOrdered hExit
  obtain ⟨lastCopy⟩ := s.prior_effective_occurrence history hLast hRight lastBad.1.isLt
  obtain ⟨data⟩ := s.actual_high_path_depth history hLast hAmbientRun path hRight
    childCopy lastCopy hSourceEvent hHigh hSourceFront
  obtain ⟨rootCopy, hEdge⟩ := s.recorded_root_parent_exists history hLast hStartRun hExit
    hRootColumn lastBad.1.isLt lastCopy
  obtain ⟨rootNode, hRootRef, hRootCell⟩ := Canonical.frame_node_of_cellAt rootCopy.result_read
  have hRootNodeColumn : rootNode.1.val = start.size - 1 :=
    (congrArg Ref.column hRootRef).trans rootCopy.reference_column
  have hRawEdge : (Frame.ofMountain ambient).rawParent data.parentNode = some rootNode :=
    hEdge.rawParent data.parent_reference hRootRef
  have hRaw := (p.blocks_raw_geometry_of_run hLast hAmbientRun).rawRowGeometry
  have hFather := (p.blocks_raw_father_bound_of_run hLast hAmbientRun).rawFatherUpperBound
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
  obtain ⟨startEvent, _, _, _, hStartCut⟩ :=
    p.blocks_high_event_correspondence hLast hStartRun hSourceEvent hHigh
  obtain ⟨startNode, hStartRef, hStartCell⟩ := Canonical.frame_node_of_cellAt rootCopy.start_read
  have hStartColumn : startNode.1.val = start.size - 1 :=
    (congrArg Ref.column hStartRef).trans rootCopy.reference_column
  have hStartWidth : 0 < start.size := (Nat.zero_le startNode.1.val).trans_lt startNode.1.isLt
  have hStartBound : start.size - 1 < start.size := by omega
  have hSameCut : (Frame.ofMountain ambient).eventCut data.targetEvent =
      (Frame.ofMountain start).eventCut startEvent := data.event_row.trans hStartCut.symm
  have hStartFront : eventFrontier s.start_valid.toOrdered startEvent startNode.1 = startNode := by
    have hFront : frontierAt s.ambient_valid.toOrdered ((Frame.ofMountain start).eventCut startEvent)
        ((Frame.ofMountain start).eventCut_one_le startEvent) rootNode.1 = rootNode := by
      simpa only [eventFrontier, hSameCut] using hRootFront
    have hColumns : start[rootNode.1.val]? = ambient[rootNode.1.val]? :=
      (s.start_preserved rootNode.1.val (hRootNodeColumn ▸ hStartBound)).symm
    exact frontierAt_of_same_column s.ambient_valid.toOrdered s.start_valid.toOrdered
      ((Frame.ofMountain start).eventCut_one_le startEvent) hFront
        (hStartRef.trans hRootRef.symm) hColumns
  have hStartDepth := p.blocks_root_depth_at_equal_events hLast hStartRun s.start_valid
    data.source_width hStartWidth hStartCut hHigh
  have hPreservedDepth := s.start_preserved.event_parentDepth s.start_valid.toOrdered s.ambient_valid.toOrdered
    hStartWidth data.target_width hSameCut hStartBound
  have hRootDepth : parentDepth (eventParentMap s.ambient_valid.toOrdered data.target_width
        (ambient.size - 1) data.targetEvent) (start.size - 1) =
      parentDepth (eventParentMap hNormal.toOrdered data.source_width
        (p.reduced.size - 1) sourceEvent) root.1.val := by
    rw [hRootColumn]
    exact hPreservedDepth.trans hStartDepth
  have hSourceSize : p.reduced.size - 1 < p.reduced.size := by have := data.source_width; omega
  have hTargetSize : ambient.size - 1 < ambient.size := by have := data.target_width; omega
  have hSourceDepth := hSourceSteps.depth
    (eventParentMap_leftward hNormal.toOrdered data.source_width hSourceSize sourceEvent)
  have hTargetDepth := hTargetSteps.depth
    (eventParentMap_leftward s.ambient_valid.toOrdered data.target_width hTargetSize data.targetEvent)
  have hWholePath : ParentPath (Frame.ofMountain p.reduced) child root :=
    path.trans (.cons hExit (.refl _))
  have hChildRight : p.root.column < child.1.val := hRight.trans_le (path.column_le hNormal.toOrdered)
  have hWhole := s.recorded_effective_path_to_root history hLast hStartRun hWholePath
    hRootColumn hChildRight child.1.isLt childCopy rootCopy
  exact ⟨{
    lastCopy := lastCopy, copied := data, rootCopy := rootCopy, rootNode := rootNode
    root_reference := hRootRef, root_cell := hRootCell, root_column := hRootNodeColumn
    root_frontier := hRootFront, source_root_frontier := hSourceRootFront
    start_width := hStartWidth, startEvent := startEvent, start_event_row := hStartCut
    startNode := startNode, start_reference := hStartRef, start_cell := hStartCell
    start_frontier := hStartFront, raw_path := hWhole
    source_steps := hSourceSteps, target_steps := hTargetSteps, root_depth := hRootDepth
    absolute_depth := by rw [hTargetDepth, hSourceDepth, hRootDepth] }⟩

private theorem path_eq_or_last_edge {F : Frame} {child root : F.Node}
    (path : ParentPath F child root) :
    child = root ∨ ∃ lastBad, ParentPath F child lastBad ∧ F.P lastBad = some root := by
  induction path with
  | refl _ => exact Or.inl rfl
  | @cons child middle root hParent rest ih =>
      rcases ih with he | ⟨lastBad, hPath, hLast⟩
      · subst middle
        exact Or.inr ⟨child, .refl _, hParent⟩
      · exact Or.inr ⟨lastBad, .cons hParent hPath, hLast⟩

/-- The last source edge and its copied occurrence need not be supplied:
any genuine source path from a right-hand child into the root column
constructs the split and the complete absolute-depth packet. -/
theorem DynamicBlockState.actual_high_root_path_depth_of_path
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies startCopies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hAmbientRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok ambient)
    {child root : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child root)
    (hRootColumn : root.1.val = p.root.column) (hChildRight : p.root.column < child.1.val)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    ∃ lastBad, ParentPath (Frame.ofMountain p.reduced) child lastBad ∧
      (Frame.ofMountain p.reduced).P lastBad = some root ∧
      Nonempty (HighRootPathDepth s child lastBad root sourceEvent childCopy) := by
  rcases path_eq_or_last_edge path with he | ⟨lastBad, hPrefix, hExit⟩
  · have hc := congrArg (fun node => node.1.val) he
    omega
  · exact ⟨lastBad, hPrefix, hExit, s.actual_high_root_path_depth history hLast hStartRun hAmbientRun
      hPrefix hExit hRootColumn childCopy hSourceEvent hHigh hSourceFront⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveRootEndpoint.reference_column
#print axioms OmegaY.Expansion.EffectiveRootEndpoint.start_read
#print axioms OmegaY.Expansion.DynamicBlockState.actual_high_root_path_depth
#print axioms OmegaY.Expansion.DynamicBlockState.actual_high_root_path_depth_of_path
