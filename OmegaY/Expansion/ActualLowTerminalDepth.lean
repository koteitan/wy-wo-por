/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowTerminalDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowPathDepth

/-!
# Absolute depth at a lifted cut for a path ending in a source top

The executed floor event contains both actual copied endpoints. A source
parentless endpoint is an actual top; its effective occurrence is also an
actual top. Their depths are zero, so equal path lengths give equality of
the starting absolute depths even below Z. No event matching is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem LowCopiedPathDepth.terminal_depths
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {child parent : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {childCopy : EffectiveCopyOccurrence p block start references child ambient}
    {parentCopy : EffectiveCopyOccurrence p block start references parent ambient}
    (packet : LowCopiedPathDepth s child parent sourceEvent childCopy parentCopy)
    (hLast : 1 < last) (hNone : (Frame.ofMountain p.reduced).P parent = none) :
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered packet.source_width
      (p.reduced.size - 1) sourceEvent) parent.1.val = 0 ∧
      parentDepth (eventParentMap s.ambient_valid.toOrdered packet.target_width
        (ambient.size - 1) packet.targetEvent) packet.parentNode.1.val = 0 ∧
      parentDepth (eventParentMap s.ambient_valid.toOrdered packet.target_width
        (ambient.size - 1) packet.targetEvent) packet.childNode.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered packet.source_width
        (p.reduced.size - 1) sourceEvent) child.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceReal : Real parent := packet.source_parent_frontier ▸
    (eventFrontier_spec hNormal.toOrdered sourceEvent parent.1).2.1
  have hSourceTop : (Frame.ofMountain p.reduced).upper parent = none := by
    cases hUpper : (Frame.ofMountain p.reduced).upper parent with
    | none => rfl
    | some upper =>
        obtain ⟨father, hFather, _⟩ := hNormal.upper_step parent upper hSourceReal hUpper
        rw [hNone] at hFather
        cases hFather
  have hTargetTop := parentCopy.top_upper_none hLast hSourceTop packet.parent_reference
  have hSourceMap : eventParentMap hNormal.toOrdered packet.source_width (p.reduced.size - 1)
      sourceEvent parent.1.val = none := by
    rw [hNormal.eventParentMap_at packet.source_width sourceEvent parent.1
      (by have hc : parent.1.val < p.reduced.size := parent.1.isLt; omega),
      packet.source_parent_frontier, hNone]
    rfl
  have hTargetMap : eventParentMap s.ambient_valid.toOrdered packet.target_width (ambient.size - 1)
      packet.targetEvent packet.parentNode.1.val = none := by
    rw [eventParentMap_raw_at s.ambient_valid.toOrdered packet.target_width packet.targetEvent packet.parentNode.1
      (by have hc : packet.parentNode.1.val < ambient.size := packet.parentNode.1.isLt; omega), packet.parent_frontier,
      Frame.rawParent_none_of_upper_none hTargetTop]
    rfl
  have hSourceDepth := parentDepth_none hSourceMap
  have hTargetDepth := parentDepth_none hTargetMap
  refine ⟨hSourceDepth, hTargetDepth, ?_⟩
  rw [packet.source_depth, packet.target_depth, hSourceDepth, hTargetDepth]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.LowCopiedPathDepth.terminal_depths


