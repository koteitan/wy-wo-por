/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFirstSplitEvent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNonmarkerSplitEvent
import OmegaY.Expansion.SourceFirstSplit

/-!+# Actual event synchronization at a first nonmarker depth difference

The one original common-parent premise and earlier equal source depths
produce the immediate predecessor's real common parent. Actual history
constructs both predecessor copies. The ensuing true contour advances
then identify a single actual target event containing both current copies.
No per-event parent equality, current parent agreement, copied numerical
recognition or target-frontier premise is imposed.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem DynamicBlockState.actual_first_split_event
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hWidth : 0 < p.reduced.size) {bound previous event : Nat} (hBound : bound < p.reduced.size)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBound : left.val ≤ bound) (hRightBound : right.val ≤ bound)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (leftCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) ambient)
    (rightCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) ambient)
    (hLeftUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left).2.val ∉
      (p.marked[left.val]?.getD []).map Ref.index)
    (hRightUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right).2.val ∉
      (p.marked[right.val]?.getD []).map Ref.index)
    (hCommon : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hStart : previous + 1 ≤ event) (hEvent : event ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hEarlier : ∀ r, previous + 1 ≤ r → r < event →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hWidth bound r) left.val =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hWidth bound r) right.val)
    (hDifferent : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hWidth bound event) left.val ≠
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hWidth bound event) right.val) :
    Nonempty (EffectiveSameRowEvent leftCopy rightCopy s.ambient_valid) := by
  obtain ⟨before, parent, hEventEq, _, hBefore, hOldLeft, hOldRight⟩ :=
    build_first_split_previous_parent p.reduced_build hWidth hBound left right hLeftBound hRightBound
      hCommon hStart hEvent hEarlier hDifferent
  subst event
  have hNormal := build_normal_of_success p.reduced_build
  have hOldLCol := (eventFrontier_spec hNormal.toOrdered before left).1
  have hOldRCol := (eventFrontier_spec hNormal.toOrdered before right).1
  have hNewLCol := (eventFrontier_spec hNormal.toOrdered (before + 1) left).1
  have hNewRCol := (eventFrontier_spec hNormal.toOrdered (before + 1) right).1
  have hLeftRight : p.root.column < left.val := by simpa only [hNewLCol] using leftCopy.state.next_lower
  have hRightRight : p.root.column < right.val := by simpa only [hNewRCol] using rightCopy.state.next_lower
  obtain ⟨oldLeftCopy⟩ := s.prior_effective_occurrence history hLast
    (show p.root.column < (eventFrontier hNormal.toOrdered before left).1.val by simpa only [hOldLCol] using hLeftRight)
    (show (eventFrontier hNormal.toOrdered before left).1.val < next by simpa only [hOldLCol] using hLeftBefore)
  obtain ⟨oldRightCopy⟩ := s.prior_effective_occurrence history hLast
    (show p.root.column < (eventFrontier hNormal.toOrdered before right).1.val by simpa only [hOldRCol] using hRightRight)
    (show (eventFrontier hNormal.toOrdered before right).1.val < next by simpa only [hOldRCol] using hRightBefore)
  exact actual_nonmarker_split_event hLast s.ambient_valid hWidth hBound hBefore left right
    hLeftBound hRightBound oldLeftCopy oldRightCopy leftCopy rightCopy hLeftUnmarked hRightUnmarked
    hOldLeft hOldRight hDifferent

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.actual_first_split_event
