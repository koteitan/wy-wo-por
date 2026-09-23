/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMixedSourceDepthOrder.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMixedBandFixedDepth

/-!
# A mixed common-candidate source pair has a forced depth orientation

The unmarked parent's source record lies strictly before the marked root
endpoint. At the common source event, its depth is therefore at most the
root depth, whereas the marked node's depth is strictly above the root.
This excludes the opposite marker orientation at a strict first split.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem ActualRootInterval.mixed_source_event_depth_lt
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {index : Nat} {row : Row}
    (a : ActualRootInterval p start ambient references index row)
    (hWidth : 0 < p.reduced.size)
    {marked other candidate : (Frame.ofMountain p.reduced).Node}
    (hMarked : BucketMem p.marked marked.1.val (Frame.ref marked))
    (hUnmarked : ¬ BucketMem p.marked other.1.val (Frame.ref other))
    (hMarkedRight : p.root.column < marked.1.val) (hOtherRight : p.root.column < other.1.val)
    (hMarkedRow : (Frame.ofMountain p.reduced).height marked = row)
    (hOtherRow : (Frame.ofMountain p.reduced).height other = row)
    (hMarkedQ : (Frame.ofMountain p.reduced).Q marked = some candidate)
    (hOtherQ : (Frame.ofMountain p.reduced).Q other = some candidate)
    {event : Nat}
    (hMarkedFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered event marked.1 = marked)
    (hOtherFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered event other.1 = other) :
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hWidth (p.reduced.size - 1) event) other.1.val <
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hWidth (p.reduced.size - 1) event) marked.1.val := by
  have hNormal := build_normal_of_success p.reduced_build
  let parentMap := eventParentMap hNormal.toOrdered hWidth (p.reduced.size - 1) event
  have hBound : p.reduced.size - 1 < p.reduced.size := by omega
  have hLeftward : Leftward parentMap := eventParentMap_leftward hNormal.toOrdered hWidth hBound event
  have hMarkedBound : marked.1.val ≤ p.reduced.size - 1 := by
    have hc : marked.1.val < p.reduced.size := marked.1.isLt
    omega
  have hOtherBound : other.1.val ≤ p.reduced.size - 1 := by
    have hc : other.1.val < p.reduced.size := other.1.isLt
    omega
  have hRootBound : a.root.1.val ≤ p.reduced.size - 1 := by
    have hc : a.root.1.val < p.reduced.size := a.root.1.isLt
    omega
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  obtain ⟨low, _, hLowColumn, hLowRow, hPath⟩ := a.rootCone_of_marker hMarked hMarkedRow
  have hLowEq : low = marked := node_eq_of_column_height hNormal.toOrdered hLowColumn
    (hLowRow.trans (a.root_row.trans hMarkedRow.symm))
  subst low
  have hRootFront := hNormal.parentPath_eventFrontier event hMarkedFront hPath
  have hMarkedAncestor : Ancestor parentMap marked.1.val a.root.1.val := by
    rcases hNormal.parentPath_eventParentMap hWidth hMarkedFront hMarkedBound hPath with he | ha
    · have hc := congrArg (fun node => node.1.val) he
      omega
    · exact ha
  have hRootLt : parentDepth parentMap a.root.1.val < parentDepth parentMap marked.1.val :=
    ancestor_depth_lt (parent := parentMap) hLeftward hMarkedAncestor
  have hOtherLe : parentDepth parentMap other.1.val ≤ parentDepth parentMap a.root.1.val := by
    cases hParent : (Frame.ofMountain p.reduced).P other with
    | none =>
      have hMap : parentMap other.1.val = none := by
        dsimp only [parentMap]
        rw [hNormal.eventParentMap_at hWidth event other.1 hOtherBound, hOtherFront, hParent]
        rfl
      rw [parentDepth_none hMap]
      exact Nat.zero_le _
    | some parent =>
      obtain ⟨path, hFixed⟩ := a.mixed_candidate_parent_exit hMarked hUnmarked hMarkedRight hOtherRight
        hMarkedRow hOtherRow hMarkedQ hOtherQ hParent
      have hAncestor : Ancestor parentMap a.root.1.val parent.1.val := by
        rcases hNormal.parentPath_eventParentMap hWidth hRootFront hRootBound path with he | ha
        · have hc := congrArg (fun node => node.1.val) he
          omega
        · exact ha
      have hParentLt : parentDepth parentMap parent.1.val < parentDepth parentMap a.root.1.val :=
        ancestor_depth_lt (parent := parentMap) hLeftward hAncestor
      have hMap : parentMap other.1.val = some parent.1.val := by
        dsimp only [parentMap]
        rw [hNormal.eventParentMap_at hWidth event other.1 hOtherBound, hOtherFront, hParent]
        rfl
      have hDepth : parentDepth parentMap other.1.val = parentDepth parentMap parent.1.val + 1 :=
        parentDepth_some (parent := parentMap) hLeftward hMap
      omega
  exact hOtherLe.trans_lt hRootLt

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualRootInterval.mixed_source_event_depth_lt
