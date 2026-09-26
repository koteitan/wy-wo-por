/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSourceFork.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSourceRootIndicators
import OmegaY.Expansion.CanonicalEventProjection

/-!
# A typed source fork at the first depth difference

The actual source's previous common parent and earlier equal event depths
construct a path from the deeper frontier to the shallower frontier's
parent. This source fact has no root-column restriction and supplies no
target path, target frontier or output normality assumption.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem build_source_parent_fork_at_first_difference
    {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    (left right : Fin (Frame.ofMountain mountain).width)
    {previous event : Nat}
    (hCommon : (Frame.ofMountain mountain).P
        (eventFrontier (build_normal_of_success hBuild).toOrdered previous left) =
      (Frame.ofMountain mountain).P
        (eventFrontier (build_normal_of_success hBuild).toOrdered previous right))
    (hStart : previous + 1 ≤ event) (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (hEarlier : ∀ r, previous + 1 ≤ r → r < event →
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth
          (mountain.size - 1) r) left.val =
        parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth
          (mountain.size - 1) r) right.val)
    (hOrder : parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth
          (mountain.size - 1) event) left.val ≤
        parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth
          (mountain.size - 1) event) right.val)
    {parent : (Frame.ofMountain mountain).Node}
    (hParent : (Frame.ofMountain mountain).P
      (eventFrontier (build_normal_of_success hBuild).toOrdered event left) = some parent) :
    ParentPath (Frame.ofMountain mountain)
      (eventFrontier (build_normal_of_success hBuild).toOrdered event left) parent ∧
    ParentPath (Frame.ofMountain mountain)
      (eventFrontier (build_normal_of_success hBuild).toOrdered event right) parent := by
  have hNormal := build_normal_of_success hBuild
  have hBound : mountain.size - 1 < mountain.size := by omega
  have hLB : left.val ≤ mountain.size - 1 := by
    have hc : left.val < mountain.size := left.isLt; omega
  have hRB : right.val ≤ mountain.size - 1 := by
    have hc : right.val < mountain.size := right.isLt; omega
  have hParentFront := hNormal.eventFrontier_parent event left hParent
  have hMap : eventParentMap hNormal.toOrdered hWidth (mountain.size - 1) event left.val = some parent.1.val := by
    rw [hNormal.eventParentMap_at hWidth event left hLB, hParent]
    rfl
  have hAncestor := build_source_root_ancestor_at_first_difference hBuild hWidth
    hBound left right hLB hRB hCommon hStart hEvent hEarlier hOrder (.single hMap)
  have hPath := hNormal.parentPath_of_eventParentMap_ancestor hWidth hBound hRB hAncestor
  rw [eventFrontierNat_eq hNormal.toOrdered hWidth event right.isLt,
    eventFrontierNat_eq hNormal.toOrdered hWidth event parent.1.isLt] at hPath
  exact ⟨.cons hParent (.refl _), by simpa only [hParentFront] using hPath⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_source_parent_fork_at_first_difference
