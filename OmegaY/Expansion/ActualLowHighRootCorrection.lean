/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowHighRootCorrection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowRootCorrection

/-!
# Zero correction at and above the bad root

At the bad root, the actual strict selector below Z has the original
root's fixed parent, or no parent. This argument allows a source cut below
Z. At higher root nodes the original frontier cut is already at least Z.
Neither case assumes that the copied graph is numerically canonical.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- The selected-root constructor's literal boundary membership forces
the actual cap to be Z at the bad root. A high-tail constructor cannot
represent that source node. -/
theorem EffectiveRootEndpoint.below_of_at_badRoot
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start result : Mountain} {references : List Ref}
    {root : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references root result)
    (hLast : 1 < last) (hAt : root.2.val = p.root.index) :
    below start (start.size - 1) p.lastTop.row = .ok endpoint.reference := by
  have hRootRef : Frame.ref root = p.root := congrArg₂ Ref.mk endpoint.source_column hAt
  have hRootCell : (Frame.ofMountain p.reduced).cell root = p.rootCell :=
    Except.ok.inj ((cellAt_of_frame_node p.reduced root).symm.trans
      (by simpa only [hRootRef] using p.restored_root))
  have hRootRow : (Frame.ofMountain p.reduced).height root = p.rootCell.row := congrArg Cell.row hRootCell
  cases endpoint with
  | selected copy =>
      obtain ⟨nodes, hNodes, _⟩ := cellAt_ok_iff.mp p.initial_root
      have hCap := p.boundary_cap_eq_lastTop hNodes copy.cap_member
        (hRootRow ▸ Row.lt_bump ((Frame.ofMountain p.reduced).height root) copy.degree)
      simpa only [EffectiveRootEndpoint.reference, hCap] using copy.start_below
  | highTail copy =>
      exact False.elim ((not_lt_of_ge (hRootRow ▸ copy.source_high)) (p.root_row_lt_top hLast))

/-- The actual highest selector has exactly the source bad-root's raw
parent, transported into the retained complete prefix. Source initial and
reduced searches agree by executable strict-left locality. -/
theorem DynamicBlockState.highest_root_endpoint_rawParent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next copies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {root : (Frame.ofMountain p.reduced).Node}
    (endpoint : EffectiveRootEndpoint p start references root ambient)
    (hAt : root.2.val = p.root.index)
    {target : (Frame.ofMountain start).Node}
    (hTargetRef : Frame.ref target = endpoint.reference) :
    (Frame.ofMountain start).rawParent target =
      ((Frame.ofMountain p.reduced).P root).map s.base_preserved.mapNode := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRootRef : Frame.ref root = p.root := congrArg₂ Ref.mk endpoint.source_column hAt
  have hSearch : findParent p.initial p.root = findParent p.reduced (Frame.ref root) := by
    rw [hRootRef]
    exact findParent_eq_of_columns (fun c hc =>
      build_changed_last_preserves_prefix p.initial_build p.reduced_build (hc.trans_lt p.root_before_last))
  have hBelow := endpoint.below_of_at_badRoot hLast hAt
  obtain ⟨reference, _, hActualBelow, _, _, hCases⟩ :=
    p.blocks_highest_classification_of_run hLast hStartRun
  have hRef : reference = endpoint.reference := Except.ok.inj (hActualBelow.symm.trans hBelow)
  rcases hCases with ⟨oldParent, hOldSearch, _, hEdge, _⟩ | ⟨hNone, terminal, hTerminal, _, _, _, _, hRaw⟩
  · have hReducedSearch : findParent p.reduced (Frame.ref root) = .ok (Frame.ref oldParent) :=
      hSearch.symm.trans hOldSearch
    obtain ⟨parent, hParent, hParentRef⟩ :=
      (Executable.findParent_iff hNormal.toOrdered root (Frame.ref oldParent)).mp hReducedSearch
    rw [hParent]
    exact hEdge.rawParent (hTargetRef.trans hRef.symm)
      ((s.base_preserved.mapNode_ref parent).trans hParentRef)
  · have hSourceNone : (Frame.ofMountain p.reduced).P root = none := by
      have hOption : ((Frame.ofMountain p.reduced).P root).map Frame.ref = none :=
        (Executable.findParent_toOption hNormal.toOrdered root).symm.trans
          ((congrArg Except.toOption hSearch).symm.trans hNone)
      cases hp : (Frame.ofMountain p.reduced).P root with
      | none => rfl
      | some parent => simp only [hp, Option.map_some] at hOption; cases hOption
    have hSame : target = terminal := Executable.ref_injective _
      (hTargetRef.trans (hRef.symm.trans hTerminal.symm))
    simpa only [hSame, hSourceNone, Option.map_none] using hRaw

theorem LowRootPathDepth.correction_zero_of_at_badRoot
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next copies : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {child lastBad root : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {childCopy : EffectiveCopyOccurrence p block start references child ambient}
    (data : LowRootPathDepth s child lastBad root sourceEvent childCopy)
    (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hAt : root.2.val = p.root.index) :
    parentDepth (eventParentMap s.start_valid.toOrdered data.start_width
        (start.size - 1) data.startEvent) (start.size - 1) =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
        (p.reduced.size - 1) sourceEvent) root.1.val ∧
    parentDepth (eventParentMap s.ambient_valid.toOrdered data.copied.target_width
        (ambient.size - 1) data.copied.targetEvent) data.copied.childNode.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
        (p.reduced.size - 1) sourceEvent) child.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRaw := (p.blocks_raw_geometry_of_run hLast hStartRun).rawRowGeometry
  have hFather := (p.blocks_raw_father_bound_of_run hLast hStartRun).rawFatherUpperBound
  have hParentMap := s.highest_root_endpoint_rawParent hLast hStartRun data.rootCopy hAt data.start_reference
  let sourceMap := eventParentMap hNormal.toOrdered data.copied.source_width (p.reduced.size - 1) sourceEvent
  let targetMap := eventParentMap s.start_valid.toOrdered data.start_width (start.size - 1) data.startEvent
  have hSourceSize : p.reduced.size - 1 < p.reduced.size := by have := data.copied.source_width; omega
  have hTargetSize : start.size - 1 < start.size := by have := data.start_width; omega
  have hSourceLeft : Leftward sourceMap := eventParentMap_leftward hNormal.toOrdered
    data.copied.source_width hSourceSize sourceEvent
  have hTargetLeft : Leftward targetMap := eventParentMap_leftward s.start_valid.toOrdered
    data.start_width hTargetSize data.startEvent
  have hRootBound : root.1.val ≤ p.reduced.size - 1 := by
    have hc : root.1.val < p.reduced.size := root.1.isLt
    omega
  have hSourceAt : sourceMap root.1.val =
      ((Frame.ofMountain p.reduced).P root).map (fun parent => parent.1.val) := by
    dsimp only [sourceMap]
    rw [hNormal.eventParentMap_at data.copied.source_width sourceEvent root.1 hRootBound,
      data.source_root_frontier]
  have hTargetAt : targetMap (start.size - 1) =
      ((Frame.ofMountain start).rawParent data.startNode).map (fun parent => parent.1.val) := by
    have hm := eventParentMap_raw_at s.start_valid.toOrdered data.start_width data.startEvent
      data.startNode.1 (show data.startNode.1.val ≤ start.size - 1 from data.start_column.le)
    simpa only [data.start_column, data.start_frontier] using hm
  have hBoundary : parentDepth targetMap (start.size - 1) = parentDepth sourceMap root.1.val := by
    cases hp : (Frame.ofMountain p.reduced).P root with
    | none =>
        have hTargetNone : (Frame.ofMountain start).rawParent data.startNode = none := by
          simpa only [hp, Option.map_none] using hParentMap
        have hs : sourceMap root.1.val = none := by simpa only [hp, Option.map_none] using hSourceAt
        have ht : targetMap (start.size - 1) = none := by
          simpa only [hTargetNone, Option.map_none] using hTargetAt
        rw [parentDepth_none ht, parentDepth_none hs]
    | some parent =>
        have hTargetParent : (Frame.ofMountain start).rawParent data.startNode =
            some (s.base_preserved.mapNode parent) := by
          simpa only [hp, Option.map_some] using hParentMap
        have hSourceFront := hNormal.eventFrontier_parent sourceEvent root.1
          (by rw [data.source_root_frontier]; exact hp)
        have hTargetFront := eventFrontier_raw_parent_of_bound s.start_valid.toOrdered hRaw hFather
          data.startEvent data.startNode.1 (by rw [data.start_frontier]; exact hTargetParent)
        have hFixed := s.base_preserved.event_parentDepth_of_common_frontier hNormal
          s.start_valid.toOrdered hRaw hFather data.copied.source_width data.start_width
            hSourceFront hTargetFront
        have hs : sourceMap root.1.val = some parent.1.val := by
          simpa only [hp, Option.map_some] using hSourceAt
        have ht : targetMap (start.size - 1) = some parent.1.val := by
          simpa only [hTargetParent, Option.map_some, s.base_preserved.mapNode_column] using hTargetAt
        rw [parentDepth_some hTargetLeft ht, parentDepth_some hSourceLeft hs]
        exact congrArg (· + 1) hFixed
  refine ⟨hBoundary, ?_⟩
  rw [data.target_depth, data.source_depth, hBoundary]

/-- Above all actual reference caps, this occurrence's cut lift resets.
The packet's floor event therefore has the source cut itself, since that
source event row is retained in the complete original prefix. -/
theorem LowRootPathDepth.correction_zero_of_high_cut
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next copies : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {child lastBad root : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {childCopy : EffectiveCopyOccurrence p block start references child ambient}
    (data : LowRootPathDepth s child lastBad root sourceEvent childCopy)
    (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent) :
    parentDepth (eventParentMap s.start_valid.toOrdered data.start_width
        (start.size - 1) data.startEvent) (start.size - 1) =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
        (p.reduced.size - 1) sourceEvent) root.1.val ∧
    parentDepth (eventParentMap s.ambient_valid.toOrdered data.copied.target_width
        (ambient.size - 1) data.copied.targetEvent) data.copied.childNode.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
        (p.reduced.size - 1) sourceEvent) child.1.val := by
  obtain ⟨degree, hTarget, hCap⟩ := childCopy.state.marker_caps_below_lastTop hLast
    childCopy.data child.1.isLt childCopy.read.marker childCopy.read.marker_mem
  have hLift : childCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) =
      (Frame.ofMountain p.reduced).eventCut sourceEvent :=
    Row.lift_eq_of_ge_cap
      (childCopy.data.marker_data childCopy.read.marker childCopy.read.marker_mem).target_lower
      hTarget (hCap.trans hHigh)
  have hMember : (Frame.ofMountain p.reduced).eventCut sourceEvent ∈ (Frame.ofMountain start).eventCuts :=
    mem_eventCuts.mpr (s.base_preserved.eventRows_subset
      (mem_eventCuts.mp ((Frame.ofMountain p.reduced).eventCut_mem sourceEvent)))
  have hCut : (Frame.ofMountain start).eventCut data.startEvent =
      (Frame.ofMountain p.reduced).eventCut sourceEvent :=
    le_antisymm (data.start_event_below.trans_eq hLift)
      (data.start_event_maximal _ hMember (le_of_eq hLift.symm))
  have hBoundary := p.blocks_root_depth_at_equal_events hLast hStartRun s.start_valid
    data.copied.source_width data.start_width hCut hHigh
  rw [← data.rootCopy.source_column] at hBoundary
  refine ⟨hBoundary, ?_⟩
  rw [data.target_depth, data.source_depth, hBoundary]

/-- Highest-root and high-tail cases are exhaustive for a source index
at or above the bad root. No high-cut condition is supplied: it follows
from the source frontier when the root index is strictly higher. -/
theorem LowRootPathDepth.correction_zero_of_at_or_above_badRoot
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next copies : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {child lastBad root : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {childCopy : EffectiveCopyOccurrence p block start references child ambient}
    (data : LowRootPathDepth s child lastBad root sourceEvent childCopy)
    (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hAfter : p.root.index ≤ root.2.val) :
    parentDepth (eventParentMap s.start_valid.toOrdered data.start_width
        (start.size - 1) data.startEvent) (start.size - 1) =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
        (p.reduced.size - 1) sourceEvent) root.1.val ∧
    parentDepth (eventParentMap s.ambient_valid.toOrdered data.copied.target_width
        (ambient.size - 1) data.copied.targetEvent) data.copied.childNode.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
        (p.reduced.size - 1) sourceEvent) child.1.val := by
  rcases eq_or_lt_of_le hAfter with hAt | hAbove
  · exact data.correction_zero_of_at_badRoot hLast hStartRun hAt.symm
  · have hRootHigh := p.root_node_after_badRoot_is_high hLast data.rootCopy.source_column hAbove
    have hRootBelow : (Frame.ofMountain p.reduced).height root ≤
        (Frame.ofMountain p.reduced).eventCut sourceEvent := data.source_root_frontier ▸
      (eventFrontier_spec (build_normal_of_success p.reduced_build).toOrdered sourceEvent root.1).2.2.1
    exact data.correction_zero_of_high_cut hLast hStartRun (hRootHigh.trans hRootBelow)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveRootEndpoint.below_of_at_badRoot
#print axioms OmegaY.Expansion.DynamicBlockState.highest_root_endpoint_rawParent
#print axioms OmegaY.Expansion.LowRootPathDepth.correction_zero_of_at_badRoot
#print axioms OmegaY.Expansion.LowRootPathDepth.correction_zero_of_high_cut
#print axioms OmegaY.Expansion.LowRootPathDepth.correction_zero_of_at_or_above_badRoot
