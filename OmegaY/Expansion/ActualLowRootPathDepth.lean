/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowRootPathDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowPathDepth
import OmegaY.Expansion.ActualHighRootPathDepth

/-!
# Actual low-root depth balance

A copied source path reaches the actual block-start root endpoint through
its recorded final stored edge. Both the current mountain and block start
use their own actual floor events at the child's lifted cut. Their event
rows need not agree. Complete-column preservation identifies all frontiers
of the retained prefix at that common cut and preserves their depths.

The resulting balance keeps the actual start-boundary depth as a correction
term. It does not assert that this low-cut depth equals the source root's
depth, nor does it assume output numerical-parent recovery.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- Shared frontier cuts, rather than equal event rows, suffice for the
preserved prefix's actual event maps to agree. -/
theorem PreservesColumns.eventParentMap_at_common_cut {before after : Mountain}
    (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    (hSourceWidth : 0 < before.size) (hTargetWidth : 0 < after.size)
    {cut : Row} (hCut : (1 : Row) ≤ cut) {sourceEvent targetEvent : Nat}
    (hSourceFront : ∀ column, eventFrontier hBefore sourceEvent column = frontierAt hBefore cut hCut column)
    (hTargetFront : ∀ column, eventFrontier hAfter targetEvent column = frontierAt hAfter cut hCut column)
    {column : Nat} (hColumn : column < before.size) :
    eventParentMap hAfter hTargetWidth (after.size - 1) targetEvent column =
      eventParentMap hBefore hSourceWidth (before.size - 1) sourceEvent column := by
  let sourceColumn : Fin (Frame.ofMountain before).width := ⟨column, hColumn⟩
  let old := eventFrontier hBefore sourceEvent sourceColumn
  have hOldColumn : old.1.val = column := congrArg Fin.val (eventFrontier_spec hBefore sourceEvent sourceColumn).1
  have hNewColumn : (h.mapNode old).1.val = column := (h.mapNode_column old).trans hOldColumn
  have hTargetColumn : column < after.size := hNewColumn ▸ (h.mapNode old).1.isLt
  have hTargetBound : (h.mapNode old).1.val ≤ after.size - 1 := by rw [hNewColumn]; omega
  have hSourceBound : sourceColumn.val ≤ before.size - 1 := by change column ≤ before.size - 1; omega
  have hFront : eventFrontier hAfter targetEvent (h.mapNode old).1 = h.mapNode old := by
    rw [hTargetFront]
    have hAt := h.mapNode_frontierAt hBefore hAfter hCut sourceColumn
    simpa only [← hSourceFront sourceColumn] using hAt
  have hTargetMap := eventParentMap_raw_at hAfter hTargetWidth targetEvent (h.mapNode old).1 hTargetBound
  rw [hNewColumn, hFront, h.mapNode_rawParent_eq hBefore old] at hTargetMap
  rw [hTargetMap, eventParentMap_raw_at hBefore hSourceWidth sourceEvent sourceColumn hSourceBound]
  change (((Frame.ofMountain before).rawParent old).map h.mapNode).map (fun p => p.1.val) =
    ((Frame.ofMountain before).rawParent old).map (fun p => p.1.val)
  cases hParent : (Frame.ofMountain before).rawParent old with
  | none => rfl
  | some parent => simp only [Option.map_some, h.mapNode_column]

/-- The two actual event indices may have different event rows. Their
common-cut frontiers already determine identical retained parent chains. -/
theorem PreservesColumns.event_parentDepth_at_common_cut {before after : Mountain}
    (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    (hSourceWidth : 0 < before.size) (hTargetWidth : 0 < after.size)
    {cut : Row} (hCut : (1 : Row) ≤ cut) {sourceEvent targetEvent : Nat}
    (hSourceFront : ∀ column, eventFrontier hBefore sourceEvent column = frontierAt hBefore cut hCut column)
    (hTargetFront : ∀ column, eventFrontier hAfter targetEvent column = frontierAt hAfter cut hCut column)
    {column : Nat} (hColumn : column < before.size) :
    parentDepth (eventParentMap hAfter hTargetWidth (after.size - 1) targetEvent) column =
      parentDepth (eventParentMap hBefore hSourceWidth (before.size - 1) sourceEvent) column := by
  apply parentDepth_congr_below (eventParentMap_leftward hAfter hTargetWidth
    (show after.size - 1 < (Frame.ofMountain after).width by change after.size - 1 < after.size; omega) targetEvent)
  intro index hIndex
  exact h.eventParentMap_at_common_cut hBefore hAfter hSourceWidth hTargetWidth hCut
    hSourceFront hTargetFront (hIndex.trans_lt hColumn)

structure LowRootPathDepth {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (child lastBad root : (Frame.ofMountain p.reduced).Node) (sourceEvent : Nat)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient) where
  lastCopy : EffectiveCopyOccurrence p block start references lastBad ambient
  copied : LowCopiedPathDepth s child lastBad sourceEvent childCopy lastCopy
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
  start_event_end : startEvent ≤ (Frame.ofMountain start).lastEvent
  start_event_below : (Frame.ofMountain start).eventCut startEvent ≤
    childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)
  start_event_maximal : ∀ row ∈ (Frame.ofMountain start).eventCuts,
    row ≤ childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) →
      row ≤ (Frame.ofMountain start).eventCut startEvent
  start_frontiers_at_cut : ∀ column,
    eventFrontier s.start_valid.toOrdered startEvent column =
      frontierAt s.start_valid.toOrdered
        (childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) copied.cut_one column
  startNode : (Frame.ofMountain start).Node
  start_reference : Frame.ref startNode = rootCopy.reference
  start_cell : (Frame.ofMountain start).cell startNode = rootCopy.target
  start_column : startNode.1.val = start.size - 1
  start_frontier : eventFrontier s.start_valid.toOrdered startEvent startNode.1 = startNode
  raw_path : RawRefPath ambient childCopy.outputRef rootCopy.reference
  source_steps : Forests.ParentSteps
    (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
      (p.reduced.size - 1) sourceEvent) child.1.val root.1.val (copied.length + 1)
  target_steps : Forests.ParentSteps
    (eventParentMap s.ambient_valid.toOrdered copied.target_width (ambient.size - 1) copied.targetEvent)
      copied.childNode.1.val (start.size - 1) (copied.length + 1)
  boundary_depth :
    parentDepth (eventParentMap s.ambient_valid.toOrdered copied.target_width
      (ambient.size - 1) copied.targetEvent) (start.size - 1) =
    parentDepth (eventParentMap s.start_valid.toOrdered start_width
      (start.size - 1) startEvent) (start.size - 1)
  source_depth :
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
      (p.reduced.size - 1) sourceEvent) child.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
      (p.reduced.size - 1) sourceEvent) root.1.val + (copied.length + 1)
  target_depth :
    parentDepth (eventParentMap s.ambient_valid.toOrdered copied.target_width
      (ambient.size - 1) copied.targetEvent) copied.childNode.1.val =
    parentDepth (eventParentMap s.start_valid.toOrdered start_width
      (start.size - 1) startEvent) (start.size - 1) + (copied.length + 1)
  depth_balance :
    parentDepth (eventParentMap s.ambient_valid.toOrdered copied.target_width
      (ambient.size - 1) copied.targetEvent) copied.childNode.1.val +
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
        (p.reduced.size - 1) sourceEvent) root.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
        (p.reduced.size - 1) sourceEvent) child.1.val +
      parentDepth (eventParentMap s.start_valid.toOrdered start_width
        (start.size - 1) startEvent) (start.size - 1)

/-- A real copied path followed by its source edge into the root column
determines the exact boundary correction at the child's own lifted cut. -/
theorem DynamicBlockState.actual_low_root_path_depth
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
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    Nonempty (LowRootPathDepth s child lastBad root sourceEvent childCopy) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRight : p.root.column < lastBad.1.val := hRootColumn ▸ P_column_lt hNormal.toOrdered hExit
  have hLastBefore : lastBad.1.val < next := (path.column_le hNormal.toOrdered).trans_lt hBefore
  obtain ⟨lastCopy⟩ := s.prior_effective_occurrence history hLast hRight hLastBefore
  obtain ⟨data⟩ := s.actual_low_path_depth history hLast hStartRun path hRight hBefore
    childCopy lastCopy hUnmarked hSourceEvent hSourceFront
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

private theorem low_path_eq_or_last_edge {F : Frame} {child root : F.Node}
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
theorem DynamicBlockState.actual_low_root_path_depth_of_path
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
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    ∃ lastBad, ParentPath (Frame.ofMountain p.reduced) child lastBad ∧
      (Frame.ofMountain p.reduced).P lastBad = some root ∧
      Nonempty (LowRootPathDepth s child lastBad root sourceEvent childCopy) := by
  rcases low_path_eq_or_last_edge path with he | ⟨lastBad, hPrefix, hExit⟩
  · have hc := congrArg (fun node => node.1.val) he
    omega
  · exact ⟨lastBad, hPrefix, hExit, s.actual_low_root_path_depth history hLast hStartRun
      hPrefix hExit hRootColumn hBefore childCopy hUnmarked hSourceEvent hSourceFront⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.eventParentMap_at_common_cut
#print axioms OmegaY.Expansion.PreservesColumns.event_parentDepth_at_common_cut
#print axioms OmegaY.Expansion.DynamicBlockState.actual_low_root_path_depth
#print axioms OmegaY.Expansion.DynamicBlockState.actual_low_root_path_depth_of_path
