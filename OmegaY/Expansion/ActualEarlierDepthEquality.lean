/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEarlierDepthEquality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentDepth
import OmegaY.Expansion.SourceFirstSplit

/-!
# Earlier equal source depths at actual paired target frontiers

Source numeric recovery first turns the initial common P and all equal
depths through the selected event into actual typed P equality there.
The actual copied common-parent theorem then gives target depth equality
at every event containing the two effective copies. The final source
event is covered by its genuine parentless tops.

This is a pointwise transport lemma. It does not assert that such paired
frontiers cover every target event between consecutive source samples.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem build_source_parent_eq_after_equal_depths
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
    (hEqual : parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth
          (mountain.size - 1) event) left.val =
        parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth
          (mountain.size - 1) event) right.val) :
    (Frame.ofMountain mountain).P (eventFrontier (build_normal_of_success hBuild).toOrdered event left) =
      (Frame.ofMountain mountain).P (eventFrontier (build_normal_of_success hBuild).toOrdered event right) := by
  have hNormal := build_normal_of_success hBuild
  by_cases hLast : event = (Frame.ofMountain mountain).lastEvent
  · subst event
    have hLeft := (hNormal.rawParent_eq_P
      (eventFrontier_spec hNormal.toOrdered (Frame.ofMountain mountain).lastEvent left).2.1).symm.trans
        (rawParent_none_of_upper_none (eventFrontier_last_upper_none hNormal.toOrdered left))
    have hRight := (hNormal.rawParent_eq_P
      (eventFrontier_spec hNormal.toOrdered (Frame.ofMountain mountain).lastEvent right).2.1).symm.trans
        (rawParent_none_of_upper_none (eventFrontier_last_upper_none hNormal.toOrdered right))
    exact hLeft.trans hRight.symm
  · have hBound : mountain.size - 1 < mountain.size := by omega
    have hLB : left.val ≤ mountain.size - 1 := by
      have hc : left.val < mountain.size := left.isLt; omega
    have hRB : right.val ≤ mountain.size - 1 := by
      have hc : right.val < mountain.size := right.isLt; omega
    have hParents := build_candidate_parent_at_first_difference hBuild hWidth hBound hLB hRB
      (build_common_frontier_candidate_parent hBuild hWidth left right hLB hRB hCommon)
      (show previous + 1 ≤ event + 1 by omega)
      (show event + 1 ≤ (Frame.ofMountain mountain).lastEvent by omega)
      (fun r hr hre => by
        by_cases he : r = event
        · simpa only [he] using hEqual
        · exact hEarlier r hr (by omega))
    change eventParentMap hNormal.toOrdered hWidth (mountain.size - 1) event left.val =
      eventParentMap hNormal.toOrdered hWidth (mountain.size - 1) event right.val at hParents
    exact hNormal.P_eq_of_eventParentMap_eq hWidth left right hLB hRB hParents

theorem DynamicBlockState.equal_depth_at_paired_frontiers
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {left right : (Frame.ofMountain p.reduced).Node}
    (hLeftBefore : left.1.val < next) (hRightBefore : right.1.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references left ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references right ambient)
    {leftNode rightNode : (Frame.ofMountain ambient).Node}
    (hLeftRef : Frame.ref leftNode = leftCopy.outputRef)
    (hRightRef : Frame.ref rightNode = rightCopy.outputRef)
    {previous sourceEvent targetEvent : Nat}
    (hCommon : (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left.1) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right.1))
    (hStart : previous + 1 ≤ sourceEvent)
    (hEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hEarlier : ∀ event, previous + 1 ≤ event → event < sourceEvent →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) event) left.1.val =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) event) right.1.val)
    (hSourceLeft : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent left.1 = left)
    (hSourceRight : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right.1 = right)
    (hTargetLeft : eventFrontier s.ambient_valid.toOrdered targetEvent leftNode.1 = leftNode)
    (hTargetRight : eventFrontier s.ambient_valid.toOrdered targetEvent rightNode.1 = rightNode)
    (hEqual : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) sourceEvent) left.1.val =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
          (p.reduced.size - 1) sourceEvent) right.1.val) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        leftNode.1.val =
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        rightNode.1.val := by
  have hParents := build_source_parent_eq_after_equal_depths p.reduced_build hSourceWidth left.1 right.1
    hCommon hStart hEvent hEarlier hEqual
  have hTyped : (Frame.ofMountain p.reduced).P left = (Frame.ofMountain p.reduced).P right :=
    by simpa only [hSourceLeft, hSourceRight] using hParents
  exact s.depth_eq_of_source_parent_eq history hLast hStartRun hLeftBefore hRightBefore leftCopy rightCopy
    hLeftRef hRightRef hSourceWidth hTargetWidth hEvent hSourceLeft hSourceRight hTargetLeft hTargetRight hTyped

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_source_parent_eq_after_equal_depths
#print axioms OmegaY.Expansion.DynamicBlockState.equal_depth_at_paired_frontiers
