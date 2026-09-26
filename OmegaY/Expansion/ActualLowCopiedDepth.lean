/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowCopiedDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowTerminalDepth
import OmegaY.Expansion.ActualFixedExitLift
import OmegaY.Expansion.ActualLowRootCorrection
import OmegaY.Expansion.ActualLowHighRootCorrection
import OmegaY.Geometry.ParentExit

/-!
# Actual nonnegative depth correction at a copied frontier's own lift

This certificate combines all exits of an actual source parent chain.
Terminal and fixed-prefix exits have zero correction. A root-column exit
has a natural correction below the bad root and zero correction at or above
it. The target event is the actual floor of the executed contour cut.

This is a local statement about stored-parent event depth for one source
frontier. It asserts neither a shared sampling between different columns,
numerical parent recognition, nor descent along successive expansions.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

structure LowCopiedDepth {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (source : (Frame.ofMountain p.reduced).Node) (sourceEvent : Nat)
    (copy : EffectiveCopyOccurrence p block start references source ambient) where
  source_width : 0 < p.reduced.size
  target_width : 0 < ambient.size
  targetEvent : Nat
  targetNode : (Frame.ofMountain ambient).Node
  increment : Nat
  source_event_end : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent
  target_event_end : targetEvent ≤ (Frame.ofMountain ambient).lastEvent
  cut_one : (1 : Row) ≤ copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)
  target_event_below : (Frame.ofMountain ambient).eventCut targetEvent ≤
    copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)
  target_event_maximal : ∀ row ∈ (Frame.ofMountain ambient).eventCuts,
    row ≤ copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) →
      row ≤ (Frame.ofMountain ambient).eventCut targetEvent
  all_frontiers_at_cut : ∀ column,
    eventFrontier s.ambient_valid.toOrdered targetEvent column =
      frontierAt s.ambient_valid.toOrdered
        (copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) cut_one column
  reference : Frame.ref targetNode = copy.outputRef
  cell : (Frame.ofMountain ambient).cell targetNode = copy.read.outputCell
  frontier : eventFrontier s.ambient_valid.toOrdered targetEvent targetNode.1 = targetNode
  depth_eq : parentDepth
      (eventParentMap s.ambient_valid.toOrdered target_width (ambient.size - 1) targetEvent)
        targetNode.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered source_width
      (p.reduced.size - 1) sourceEvent) source.1.val + increment

def LowCopiedPathDepth.toCorrected
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {source parent : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {copy : EffectiveCopyOccurrence p block start references source ambient}
    {parentCopy : EffectiveCopyOccurrence p block start references parent ambient}
    (packet : LowCopiedPathDepth s source parent sourceEvent copy parentCopy)
    (increment : Nat)
    (hDepth : parentDepth
        (eventParentMap s.ambient_valid.toOrdered packet.target_width (ambient.size - 1) packet.targetEvent)
          packet.childNode.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered packet.source_width
        (p.reduced.size - 1) sourceEvent) source.1.val + increment) :
    LowCopiedDepth s source sourceEvent copy where
  source_width := packet.source_width
  target_width := packet.target_width
  targetEvent := packet.targetEvent
  targetNode := packet.childNode
  increment := increment
  source_event_end := packet.source_event_end
  target_event_end := packet.target_event_end
  cut_one := packet.cut_one
  target_event_below := packet.target_event_below
  target_event_maximal := packet.target_event_maximal
  all_frontiers_at_cut := packet.all_frontiers_at_cut
  reference := packet.child_reference
  cell := packet.child_cell
  frontier := packet.child_frontier
  depth_eq := hDepth

/-- The actual source-root index decides the correction; no output depth
inequality or selected-reference constructor is an input. -/
theorem LowRootPathDepth.correction
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
      pure (.yield next)) : Result Mountain) = .ok start) :
    ∃ increment,
      parentDepth (eventParentMap s.start_valid.toOrdered data.start_width
          (start.size - 1) data.startEvent) (start.size - 1) =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
          (p.reduced.size - 1) sourceEvent) root.1.val + increment ∧
      parentDepth (eventParentMap s.ambient_valid.toOrdered data.copied.target_width
          (ambient.size - 1) data.copied.targetEvent) data.copied.childNode.1.val =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered data.copied.source_width
          (p.reduced.size - 1) sourceEvent) child.1.val + increment := by
  by_cases hBefore : root.2.val < p.root.index
  · exact data.correction_of_below_badRoot hLast hStartRun hBefore
  · obtain ⟨hBoundary, hChild⟩ := data.correction_zero_of_at_or_above_badRoot
      hLast hStartRun (Nat.le_of_not_gt hBefore)
    exact ⟨0, by simpa only [Nat.add_zero] using hBoundary,
      by simpa only [Nat.add_zero] using hChild⟩

/-- Every nonmarker source frontier has a real copied frontier whose
absolute stored-parent depth is its source depth plus a natural number.
The three parent-path exits are exhaustive and constructed internally. -/
theorem DynamicBlockState.actual_low_copied_depth
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
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
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
    obtain ⟨packet⟩ := s.actual_low_path_depth history hLast hStartRun path hTerminalRight hBefore
      copy terminalCopy hUnmarked hSourceEvent hSourceFront
    exact ⟨packet.toCorrected 0 (by simpa only [Nat.add_zero] using
      (packet.terminal_depths hLast hNone).2.2)⟩
  · obtain ⟨lastBad, _, _, ⟨packet⟩⟩ := s.actual_low_root_path_depth_of_path history hLast
      hStartRun path hRootColumn hRight hBefore copy hUnmarked hSourceEvent hSourceFront
    obtain ⟨increment, _, hDepth⟩ := packet.correction hLast hStartRun
    exact ⟨packet.copied.toCorrected increment hDepth⟩
  · obtain ⟨packet⟩ := s.actual_low_fixed_path_depth history hLast hStartRun path hExit
      hBadRight hFixed hBefore copy hUnmarked hSourceEvent hSourceFront
    exact ⟨packet.copied.toCorrected 0 (by simpa only [Nat.add_zero] using packet.absolute_depth)⟩

theorem LowCopiedDepth.source_depth_le
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {source : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {copy : EffectiveCopyOccurrence p block start references source ambient}
    (packet : LowCopiedDepth s source sourceEvent copy) :
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered packet.source_width
        (p.reduced.size - 1) sourceEvent) source.1.val ≤
      parentDepth (eventParentMap s.ambient_valid.toOrdered packet.target_width
        (ambient.size - 1) packet.targetEvent) packet.targetNode.1.val := by
  rw [packet.depth_eq]
  exact Nat.le_add_right _ _

end OmegaY.Expansion

#print axioms OmegaY.Expansion.LowRootPathDepth.correction
#print axioms OmegaY.Expansion.DynamicBlockState.actual_low_copied_depth
#print axioms OmegaY.Expansion.LowCopiedDepth.source_depth_le
