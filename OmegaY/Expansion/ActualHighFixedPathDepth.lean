/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighFixedPathDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighPathDepth
import OmegaY.Expansion.PreservedEventDepth

/-!
# Absolute high-event depth for copied paths exiting into the fixed prefix

The copied part has the source path's edge count. Its final genuine stored
edge reaches the original fixed parent, whose complete preserved prefix
has unchanged depth at the same cut. Hence the copied child's absolute
event depth is exactly the source child's depth.

The maps here are `eventParentMap event`, corresponding to
`frontierForests (event + 1)`. No identification with a differently indexed
sampled depth word, or with newly recognized numerical parents, is made.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

structure HighFixedPathDepth {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (child lastBad fixedParent : (Frame.ofMountain p.reduced).Node) (sourceEvent : Nat)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient) where
  lastCopy : EffectiveCopyOccurrence p block start references lastBad ambient
  copied : HighCopiedPathDepth s child lastBad sourceEvent childCopy lastCopy
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

/-- A completely copied high-frontier path followed by one actual source
edge into the fixed good part has unchanged absolute depth. The old fixed
parent depth is proved from complete preservation, not supplied. -/
theorem DynamicBlockState.actual_high_fixed_path_depth
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references p.reduced.size ambient)
    (history : CopyRunHistory p block start references p.reduced.size ambient) (hLast : 1 < last)
    (hAmbientRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok ambient)
    {child lastBad fixedParent : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child lastBad)
    (hExit : (Frame.ofMountain p.reduced).P lastBad = some fixedParent)
    (hRight : p.root.column < lastBad.1.val) (hFixed : fixedParent.1.val < p.root.column)
    (childCopy : EffectiveCopyOccurrence p block start references child ambient)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent child.1 = child) :
    Nonempty (HighFixedPathDepth s child lastBad fixedParent sourceEvent childCopy) := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨lastCopy⟩ := s.prior_effective_occurrence history hLast hRight lastBad.1.isLt
  obtain ⟨data⟩ := s.actual_high_path_depth history hLast hAmbientRun path hRight
    childCopy lastCopy hSourceEvent hHigh hSourceFront
  obtain ⟨hEdge, _⟩ := s.recorded_fixed_parent history hLast hExit hRight lastBad.1.isLt hFixed lastCopy
  let fixedNode := s.base_ambient.mapNode fixedParent
  have hFixedRef : Frame.ref fixedNode = Frame.ref fixedParent := s.base_ambient.mapNode_ref fixedParent
  have hFixedCell : (Frame.ofMountain ambient).cell fixedNode =
      (Frame.ofMountain p.reduced).cell fixedParent := s.base_ambient.mapNode_cell fixedParent
  have hFixedColumn : fixedNode.1.val = fixedParent.1.val := s.base_ambient.mapNode_column fixedParent
  have hRawEdge : (Frame.ofMountain ambient).rawParent data.parentNode = some fixedNode :=
    hEdge.rawParent data.parent_reference hFixedRef
  have hRaw := (p.blocks_raw_geometry_of_run hLast hAmbientRun).rawRowGeometry
  have hFather := (p.blocks_raw_father_bound_of_run hLast hAmbientRun).rawFatherUpperBound
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
  have hFixedDepth := s.base_ambient.event_parentDepth hNormal.toOrdered s.ambient_valid.toOrdered
    data.source_width data.target_width data.event_row fixedParent.1.isLt
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
  have hWhole := (s.recorded_effective_path_to_fixed history hLast path hExit hRight
    child.1.isLt hFixed childCopy).1
  exact ⟨{
    lastCopy := lastCopy
    copied := data
    fixedNode := fixedNode
    fixed_reference := hFixedRef
    fixed_cell := hFixedCell
    fixed_frontier := hFixedFront
    source_fixed_frontier := hSourceFixedFront
    raw_path := hWhole
    source_steps := hSourceSteps
    target_steps := hTargetSteps
    fixed_depth := hFixedDepth
    absolute_depth := by rw [hTargetDepth, hSourceDepth, hFixedDepth] }⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_high_fixed_path_depth
