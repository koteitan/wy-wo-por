/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFixedExitLift.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowPathDepth
import OmegaY.Expansion.ActualHighFixedPathDepth

/-!
# Fixed exits at a genuinely lifted cut

No identity of the child's contour cut is asserted. A root cone is a
same-row shadow and does not identify the high node's actual parent chain.
Instead, complete-column preservation and actual raw frontier closure show
that a retained node which is a frontier at two possibly different cuts
has the same event depth. This is enough for the fixed-exit application.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- A shared retained frontier identifies its entire parent chain, even
when the two events have different cuts and other columns have different
frontiers. Only the original graph is assumed numerically canonical. -/
theorem PreservesColumns.event_parentDepth_of_common_frontier
    {before after : Mountain} (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Normal)
    (hAfter : (Frame.ofMountain after).Ordered)
    (hRaw : (Frame.ofMountain after).RawRowGeometry)
    (hFather : (Frame.ofMountain after).RawFatherUpperBound)
    (hSourceWidth : 0 < before.size) (hTargetWidth : 0 < after.size)
    {sourceEvent targetEvent : Nat} {node : (Frame.ofMountain before).Node}
    (hSourceFront : eventFrontier hBefore.toOrdered sourceEvent node.1 = node)
    (hTargetFront : eventFrontier hAfter targetEvent (h.mapNode node).1 = h.mapNode node) :
    parentDepth (eventParentMap hAfter hTargetWidth (after.size - 1) targetEvent) node.1.val =
      parentDepth (eventParentMap hBefore.toOrdered hSourceWidth (before.size - 1) sourceEvent)
        node.1.val := by
  let sourceMap : ParentMap := eventParentMap hBefore.toOrdered hSourceWidth (before.size - 1) sourceEvent
  let targetMap : ParentMap := eventParentMap hAfter hTargetWidth (after.size - 1) targetEvent
  have hSourceLeft : Leftward sourceMap := eventParentMap_leftward hBefore.toOrdered hSourceWidth
    (by change before.size - 1 < before.size; omega) sourceEvent
  have hTargetLeft : Leftward targetMap := eventParentMap_leftward hAfter hTargetWidth
    (by change after.size - 1 < after.size; omega) targetEvent
  change parentDepth targetMap node.1.val = parentDepth sourceMap node.1.val
  generalize hc : node.1.val = column
  induction column using Nat.strongRecOn generalizing node with
  | ind column ih =>
      have hSourceBound : node.1.val ≤ before.size - 1 := by
        have hn : node.1.val < before.size := node.1.isLt
        omega
      have hTargetBound : (h.mapNode node).1.val ≤ after.size - 1 := by
        have hn : (h.mapNode node).1.val < after.size := (h.mapNode node).1.isLt
        omega
      have hSourceMap := eventParentMap_raw_at hBefore.toOrdered hSourceWidth sourceEvent node.1 hSourceBound
      rw [hSourceFront] at hSourceMap
      have hTargetMap := eventParentMap_raw_at hAfter hTargetWidth targetEvent (h.mapNode node).1 hTargetBound
      rw [hTargetFront, h.mapNode_column, h.mapNode_rawParent_eq hBefore.toOrdered node] at hTargetMap
      change sourceMap node.1.val = _ at hSourceMap
      change targetMap node.1.val = _ at hTargetMap
      cases hp : (Frame.ofMountain before).rawParent node with
      | none =>
          have hSourceNone : sourceMap column = none := by simpa only [hc, hp, Option.map_none] using hSourceMap
          have hTargetNone : targetMap column = none := by simpa only [hc, hp, Option.map_none] using hTargetMap
          rw [parentDepth_none hTargetNone, parentDepth_none hSourceNone]
      | some parent =>
          have hReal : Real node := hSourceFront ▸ (eventFrontier_spec hBefore.toOrdered sourceEvent node.1).2.1
          have hP : (Frame.ofMountain before).P node = some parent :=
            (hBefore.rawParent_eq_P hReal).symm.trans hp
          have hSourceParentFront := hBefore.eventFrontier_parent sourceEvent node.1
            (by rw [hSourceFront]; exact hP)
          have hTargetParentFront := eventFrontier_raw_parent_of_bound hAfter hRaw hFather
            targetEvent (h.mapNode node).1 (parent := h.mapNode parent)
              (by rw [hTargetFront, h.mapNode_rawParent_eq hBefore.toOrdered node, hp]; rfl)
          have hSourceSome : sourceMap column = some parent.1.val := by
            simpa only [hc, hp, Option.map_some] using hSourceMap
          have hTargetSome : targetMap column = some parent.1.val := by
            simpa only [hc, hp, Option.map_some, h.mapNode_column] using hTargetMap
          have hLess : parent.1.val < column := by
            simpa only [hc] using P_column_lt hBefore.toOrdered hP
          rw [parentDepth_some hTargetLeft hTargetSome, parentDepth_some hSourceLeft hSourceSome,
            ih parent.1.val hLess hSourceParentFront hTargetParentFront rfl]

structure LowFixedPathDepth {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (child lastBad fixedParent : (Frame.ofMountain p.reduced).Node) (sourceEvent : Nat)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient) where
  lastCopy : EffectiveCopyOccurrence p block start references lastBad ambient
  copied : LowCopiedPathDepth s child lastBad sourceEvent childCopy lastCopy
  fixedNode : (Frame.ofMountain ambient).Node
  fixed_reference : Frame.ref fixedNode = Frame.ref fixedParent
  fixed_cell : (Frame.ofMountain ambient).cell fixedNode = (Frame.ofMountain p.reduced).cell fixedParent
  fixed_frontier : eventFrontier s.ambient_valid.toOrdered copied.targetEvent fixedNode.1 = fixedNode
  source_fixed_frontier : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
    sourceEvent fixedParent.1 = fixedParent
  raw_path : RawRefPath ambient childCopy.outputRef (Frame.ref fixedParent)
  source_steps : Forests.ParentSteps
    (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
      (p.reduced.size - 1) sourceEvent) child.1.val fixedParent.1.val (copied.length + 1)
  target_steps : Forests.ParentSteps
    (eventParentMap s.ambient_valid.toOrdered copied.target_width (ambient.size - 1) copied.targetEvent)
      copied.childNode.1.val fixedParent.1.val (copied.length + 1)
  fixed_depth :
    parentDepth (eventParentMap s.ambient_valid.toOrdered copied.target_width
      (ambient.size - 1) copied.targetEvent) fixedParent.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
      (p.reduced.size - 1) sourceEvent) fixedParent.1.val
  absolute_depth :
    parentDepth (eventParentMap s.ambient_valid.toOrdered copied.target_width
      (ambient.size - 1) copied.targetEvent) copied.childNode.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered copied.source_width
      (p.reduced.size - 1) sourceEvent) child.1.val

/-- An actual nonmarker source frontier whose parent chain exits directly
to the fixed good part has exactly the source depth at its own lifted cut.
The copied cut need not equal the source cut. All copied path edges, both
fixed-end frontiers, and their absolute depth equality are derived. -/
theorem DynamicBlockState.actual_low_fixed_path_depth
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
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    Nonempty (LowFixedPathDepth s child lastBad fixedParent sourceEvent childCopy) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hLastBefore : lastBad.1.val < next := (path.column_le hNormal.toOrdered).trans_lt hBefore
  obtain ⟨lastCopy⟩ := s.prior_effective_occurrence history hLast hRight hLastBefore
  obtain ⟨data⟩ := s.actual_low_path_depth history hLast hStartRun path hRight hBefore
    childCopy lastCopy hUnmarked hSourceEvent hSourceFront
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

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.event_parentDepth_of_common_frontier
#print axioms OmegaY.Expansion.DynamicBlockState.actual_low_fixed_path_depth
