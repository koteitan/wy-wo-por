/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualBoundaryDepthComparison.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAllSourceDepth
import OmegaY.Expansion.LowDepthTransport

/-!
# Comparing a terminal or fixed-parent frontier with another actual copy

A source top or a node whose immediate parent is in the fixed good part
has zero depth correction. Every other source frontier has a nonnegative
correction. Thus weak and strict source depth inequalities with such a
left endpoint are preserved at any target event containing both actual
effective copies. No current common-parent condition is needed here.

Selecting a common target event remains a separate geometric obligation.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem LowCopiedPathDepth.absolute_at_frontier
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {source parent : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {copy : EffectiveCopyOccurrence p block start references source ambient}
    {parentCopy : EffectiveCopyOccurrence p block start references parent ambient}
    (packet : LowCopiedPathDepth s source parent sourceEvent copy parentCopy)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hAbsolute : parentDepth (eventParentMap s.ambient_valid.toOrdered packet.target_width
          (ambient.size - 1) packet.targetEvent) packet.childNode.1.val =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered packet.source_width
          (p.reduced.size - 1) sourceEvent) source.1.val)
    {targetEvent : Nat} {node : (Frame.ofMountain ambient).Node}
    (hRef : Frame.ref node = copy.outputRef)
    (hFront : eventFrontier s.ambient_valid.toOrdered targetEvent node.1 = node) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered packet.target_width
        (ambient.size - 1) targetEvent) node.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered packet.source_width
        (p.reduced.size - 1) sourceEvent) source.1.val := by
  have hNode : packet.childNode = node := Executable.ref_injective _ (packet.child_reference.trans hRef.symm)
  let certified := packet.toCorrected 0 (by simpa only [Nat.add_zero] using hAbsolute)
  have hDepth := certified.at_frontier history hLast hStartRun
    (show eventFrontier s.ambient_valid.toOrdered targetEvent certified.targetNode.1 = certified.targetNode from
      by simpa only [certified, LowCopiedPathDepth.toCorrected, hNode] using hFront)
  simpa only [certified, LowCopiedPathDepth.toCorrected, hNode, Nat.add_zero] using hDepth

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)
  (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
  {source : (Frame.ofMountain p.reduced).Node}
  (hRight : p.root.column < source.1.val) (hBefore : source.1.val < next)
  (copy : EffectiveCopyOccurrence p block start references source ambient)
  {sourceEvent targetEvent : Nat} (hEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
  (hSource : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent source.1 = source)
  {node : (Frame.ofMountain ambient).Node}
  (hRef : Frame.ref node = copy.outputRef)
  (hTarget : eventFrontier s.ambient_valid.toOrdered targetEvent node.1 = node)

include history hLast hStartRun hRight hBefore hEvent hSource hRef hTarget

/-- Zero correction holds at any actual paired event for a source top or
a direct fixed-good-parent exit, including marked source occurrences. -/
theorem DynamicBlockState.depth_eq_of_terminal_or_fixed_parent
    (hExit : (Frame.ofMountain p.reduced).P source = none ∨
      ∃ parent, (Frame.ofMountain p.reduced).P source = some parent ∧ parent.1.val < p.root.column) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth
        (ambient.size - 1) targetEvent) node.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) source.1.val := by
  rcases hExit with hNone | ⟨parent, hParent, hFixed⟩
  · obtain ⟨packet⟩ := s.actual_all_source_path_depth history hLast hStartRun (.refl source)
      hRight hBefore copy copy hEvent hSource
    exact packet.absolute_at_frontier history hLast hStartRun
      (packet.terminal_depths hLast hNone).2.2 hRef hTarget
  · obtain ⟨packet⟩ := s.actual_all_source_fixed_path_depth history hLast hStartRun (.refl source)
      hParent hRight hFixed hBefore copy hEvent hSource
    exact packet.copied.absolute_at_frontier history hLast hStartRun packet.absolute_depth hRef hTarget

/-- Combining the proved zero correction with the other column's actual
natural correction preserves both weak and strict depth inequalities.
Their current source parents may differ and the right path may cross any
root boundary. The target event must contain the two genuine copies. -/
theorem DynamicBlockState.depth_order_of_terminal_or_fixed_left
    (hExit : (Frame.ofMountain p.reduced).P source = none ∨
      ∃ parent, (Frame.ofMountain p.reduced).P source = some parent ∧ parent.1.val < p.root.column)
    {right : (Frame.ofMountain p.reduced).Node}
    (hRightColumn : p.root.column < right.1.val) (hRightBefore : right.1.val < next)
    (rightCopy : EffectiveCopyOccurrence p block start references right ambient)
    {rightNode : (Frame.ofMountain ambient).Node}
    (hRightRef : Frame.ref rightNode = rightCopy.outputRef)
    (hSourceRight : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right.1 = right)
    (hTargetRight : eventFrontier s.ambient_valid.toOrdered targetEvent rightNode.1 = rightNode) :
    let sourceMap := eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth (p.reduced.size - 1) sourceEvent
    let targetMap := eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent
    (parentDepth sourceMap source.1.val ≤ parentDepth sourceMap right.1.val →
      parentDepth targetMap node.1.val ≤ parentDepth targetMap rightNode.1.val) ∧
    (parentDepth sourceMap source.1.val < parentDepth sourceMap right.1.val →
      parentDepth targetMap node.1.val < parentDepth targetMap rightNode.1.val) := by
  have hLeft := s.depth_eq_of_terminal_or_fixed_parent history hLast hStartRun hSourceWidth hTargetWidth
    hRight hBefore copy hEvent hSource hRef hTarget hExit
  obtain ⟨packet⟩ := s.actual_all_source_copied_depth history hLast hStartRun hRightColumn hRightBefore
    rightCopy hEvent hSourceRight
  have hNode : packet.targetNode = rightNode := Executable.ref_injective _ (packet.reference.trans hRightRef.symm)
  have hRightDepth := packet.at_frontier history hLast hStartRun
    (show eventFrontier s.ambient_valid.toOrdered targetEvent packet.targetNode.1 = packet.targetNode from
      by simpa only [hNode] using hTargetRight)
  rw [hNode] at hRightDepth
  dsimp only
  constructor <;> intro hOrder <;> omega

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.LowCopiedPathDepth.absolute_at_frontier
#print axioms OmegaY.Expansion.DynamicBlockState.depth_eq_of_terminal_or_fixed_parent
#print axioms OmegaY.Expansion.DynamicBlockState.depth_order_of_terminal_or_fixed_left
