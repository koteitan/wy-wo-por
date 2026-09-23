/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCommonParentDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualBoundaryDepthComparison
import OmegaY.Expansion.ActualRecordedRootParents

/-!
# Equal actual copied depths from equal source parents

Every common source parent maps to one common stored parent, whether it
is fixed, in the root column, or copied. At any event containing both
actual effective children this gives equal depths. The parentless case
uses actual copied tops. No target numerical recognition is required.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)
  {left right : (Frame.ofMountain p.reduced).Node}
  (hLeftBefore : left.1.val < next) (hRightBefore : right.1.val < next)
  (leftCopy : EffectiveCopyOccurrence p block start references left ambient)
  (rightCopy : EffectiveCopyOccurrence p block start references right ambient)
  {leftNode rightNode : (Frame.ofMountain ambient).Node}
  (hLeftRef : Frame.ref leftNode = leftCopy.outputRef)
  (hRightRef : Frame.ref rightNode = rightCopy.outputRef)

include s history hLast hStartRun hLeftBefore hRightBefore hLeftRef hRightRef

/-- The actual parent correspondence is independent of row-order or
overlap assumptions between the source children. -/
theorem DynamicBlockState.recorded_common_parent_nodes
    {parent : (Frame.ofMountain p.reduced).Node}
    (hLeftParent : (Frame.ofMountain p.reduced).P left = some parent)
    (hRightParent : (Frame.ofMountain p.reduced).P right = some parent) :
    ∃ father : (Frame.ofMountain ambient).Node,
      (Frame.ofMountain ambient).rawParent leftNode = some father ∧
      (Frame.ofMountain ambient).rawParent rightNode = some father := by
  rcases lt_trichotomy parent.1.val p.root.column with hFixed | hRoot | hCopied
  · obtain ⟨hLeft, hRead⟩ := s.recorded_fixed_parent history hLast hLeftParent
      leftCopy.state.next_lower hLeftBefore hFixed leftCopy
    obtain ⟨hRight, _⟩ := s.recorded_fixed_parent history hLast hRightParent
      rightCopy.state.next_lower hRightBefore hFixed rightCopy
    obtain ⟨father, hRef, _⟩ := Canonical.frame_node_of_cellAt hRead
    exact ⟨father, hLeft.rawParent hLeftRef hRef, hRight.rawParent hRightRef hRef⟩
  · obtain ⟨endpoint, hLeft, hRight⟩ := s.recorded_common_root_parent history hLast hStartRun
      hLeftParent hRightParent hRoot hLeftBefore hRightBefore leftCopy rightCopy
    obtain ⟨father, hRef, _⟩ := Canonical.frame_node_of_cellAt endpoint.result_read
    exact ⟨father, hLeft.rawParent hLeftRef hRef, hRight.rawParent hRightRef hRef⟩
  · have hBefore : parent.1.val < next :=
      (Frame.P_column_lt (build_normal_of_success p.reduced_build).toOrdered hLeftParent).trans hLeftBefore
    obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hCopied hBefore
    have hLeft := s.recorded_effective_parent history hLast hLeftParent hCopied hLeftBefore leftCopy parentCopy
    have hRight := s.recorded_effective_parent history hLast hRightParent hCopied hRightBefore rightCopy parentCopy
    obtain ⟨father, hRef, _⟩ := Canonical.frame_node_of_cellAt parentCopy.output_read
    exact ⟨father, hLeft.rawParent hLeftRef hRef, hRight.rawParent hRightRef hRef⟩

/-- Equal actual source P, including none, gives equal target frontier
depth. Target event selection is separate, and target P is not assumed. -/
theorem DynamicBlockState.depth_eq_of_source_parent_eq
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {sourceEvent targetEvent : Nat} (hEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceLeft : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent left.1 = left)
    (hSourceRight : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right.1 = right)
    (hTargetLeft : eventFrontier s.ambient_valid.toOrdered targetEvent leftNode.1 = leftNode)
    (hTargetRight : eventFrontier s.ambient_valid.toOrdered targetEvent rightNode.1 = rightNode)
    (hCommon : (Frame.ofMountain p.reduced).P left = (Frame.ofMountain p.reduced).P right) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent) leftNode.1.val =
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent) rightNode.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  cases hParent : (Frame.ofMountain p.reduced).P left with
  | none =>
      have hRightParent := hCommon.symm.trans hParent
      have hLeft := s.depth_eq_of_terminal_or_fixed_parent history hLast hStartRun hSourceWidth hTargetWidth
        leftCopy.state.next_lower hLeftBefore leftCopy hEvent hSourceLeft hLeftRef hTargetLeft (.inl hParent)
      have hRight := s.depth_eq_of_terminal_or_fixed_parent history hLast hStartRun hSourceWidth hTargetWidth
        rightCopy.state.next_lower hRightBefore rightCopy hEvent hSourceRight hRightRef hTargetRight (.inl hRightParent)
      have hLB : left.1.val ≤ p.reduced.size - 1 := by
        have hc : left.1.val < p.reduced.size := left.1.isLt; omega
      have hRB : right.1.val ≤ p.reduced.size - 1 := by
        have hc : right.1.val < p.reduced.size := right.1.isLt; omega
      have hLeftMap : eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1) sourceEvent left.1.val = none := by
        rw [hNormal.eventParentMap_at hSourceWidth sourceEvent left.1 hLB, hSourceLeft, hParent]
        rfl
      have hRightMap : eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1) sourceEvent right.1.val = none := by
        rw [hNormal.eventParentMap_at hSourceWidth sourceEvent right.1 hRB, hSourceRight, hRightParent]
        rfl
      rw [hLeft, hRight, parentDepth_none hLeftMap, parentDepth_none hRightMap]
  | some parent =>
      obtain ⟨father, hLeft, hRight⟩ := s.recorded_common_parent_nodes history hLast hStartRun
        hLeftBefore hRightBefore leftCopy rightCopy hLeftRef hRightRef hParent (hCommon.symm.trans hParent)
      have hBound : ambient.size - 1 < ambient.size := by omega
      have hLB : leftNode.1.val ≤ ambient.size - 1 := by
        have hc : leftNode.1.val < ambient.size := leftNode.1.isLt; omega
      have hRB : rightNode.1.val ≤ ambient.size - 1 := by
        have hc : rightNode.1.val < ambient.size := rightNode.1.isLt; omega
      have hLeftMap : eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1)
          targetEvent leftNode.1.val = some father.1.val := by
        rw [eventParentMap_raw_at s.ambient_valid.toOrdered hTargetWidth targetEvent leftNode.1 hLB,
          hTargetLeft, hLeft]
        rfl
      have hRightMap : eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1)
          targetEvent rightNode.1.val = some father.1.val := by
        rw [eventParentMap_raw_at s.ambient_valid.toOrdered hTargetWidth targetEvent rightNode.1 hRB,
          hTargetRight, hRight]
        rfl
      have hLeftward : Leftward (eventParentMap s.ambient_valid.toOrdered hTargetWidth
          (ambient.size - 1) targetEvent) :=
        eventParentMap_leftward s.ambient_valid.toOrdered hTargetWidth hBound targetEvent
      rw [parentDepth_some hLeftward hLeftMap, parentDepth_some hLeftward hRightMap]

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_common_parent_nodes
#print axioms OmegaY.Expansion.DynamicBlockState.depth_eq_of_source_parent_eq
