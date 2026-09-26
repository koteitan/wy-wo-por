/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SourceFirstSplit.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSourceRootIndicators
import OmegaY.Expansion.ActualSplitEvent

/-!+# The actual predecessor of a first source depth difference

Numerical source recovery propagates the initial common parent through
earlier equal depths. At the event immediately before a first difference,
equality of parent columns identifies the same typed parent because both
parents are actual frontiers of that event. The common parent cannot be
absent: two parentless canonical frontiers are tops and remain unchanged.
This supplies the real predecessor-parent input for split-event copying.
-/

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

theorem Normal.P_eq_of_eventParentMap_eq {F : Frame} (hF : F.Normal)
    (hWidth : 0 < F.width) {bound event : Nat} (left right : Fin F.width)
    (hLeft : left.val ≤ bound) (hRight : right.val ≤ bound)
    (hMaps : eventParentMap hF.toOrdered hWidth bound event left.val =
      eventParentMap hF.toOrdered hWidth bound event right.val) :
    F.P (eventFrontier hF.toOrdered event left) = F.P (eventFrontier hF.toOrdered event right) := by
  rw [hF.eventParentMap_at hWidth event left hLeft,
    hF.eventParentMap_at hWidth event right hRight] at hMaps
  cases hl : F.P (eventFrontier hF.toOrdered event left) with
  | none =>
      cases hr : F.P (eventFrontier hF.toOrdered event right) with
      | none => rfl
      | some rp => simp only [hl, hr, Option.map_none, Option.map_some] at hMaps; cases hMaps
  | some lp =>
      cases hr : F.P (eventFrontier hF.toOrdered event right) with
      | none => simp only [hl, hr, Option.map_none, Option.map_some] at hMaps; cases hMaps
      | some rp =>
          have hColumns : lp.1 = rp.1 := Fin.ext (by
            simpa only [hl, hr, Option.map_some, Option.some.injEq] using hMaps)
          have hLP := hF.eventFrontier_parent event left hl
          have hRP := hF.eventFrontier_parent event right hr
          have he : lp = rp := hLP.symm.trans ((congrArg (eventFrontier hF.toOrdered event) hColumns).trans hRP)
          exact congrArg some he

theorem Normal.eventFrontier_stable_of_parent_none {F : Frame} (hF : F.Normal)
    {first last : Nat} (hOrder : first ≤ last) (column : Fin F.width)
    (hNone : F.P (eventFrontier hF.toOrdered first column) = none) :
    eventFrontier hF.toOrdered last column = eventFrontier hF.toOrdered first column := by
  have hSpec := eventFrontier_spec hF.toOrdered first column
  have hTop : F.upper (eventFrontier hF.toOrdered first column) = none := by
    cases hu : F.upper (eventFrontier hF.toOrdered first column) with
    | none => rfl
    | some upper =>
        obtain ⟨parent, hp, _⟩ := hF.upper_step _ upper hSpec.2.1 hu
        rw [hNone] at hp
        cases hp
  rw [← hSpec.1]
  apply frontierAt_eq_of_upper_barrier hF.toOrdered (F.eventCut_one_le last)
  · exact hSpec.2.2.1.trans (F.eventCut_monotone hOrder)
  · intro upper hUpper
    rw [hTop] at hUpper
    cases hUpper

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem build_first_split_previous_parent
    {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound previous event : Nat} (hBound : bound < mountain.size)
    (left right : Fin (Frame.ofMountain mountain).width)
    (hLeftBound : left.val ≤ bound) (hRightBound : right.val ≤ bound)
    (hCommon : (Frame.ofMountain mountain).P
      (eventFrontier (build_normal_of_success hBuild).toOrdered previous left) =
      (Frame.ofMountain mountain).P
        (eventFrontier (build_normal_of_success hBuild).toOrdered previous right))
    (hStart : previous + 1 ≤ event) (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (hEarlier : ∀ r, previous + 1 ≤ r → r < event →
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound r) left.val =
        parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound r) right.val)
    (hDifferent : parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val ≠
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val) :
    ∃ (before : Nat) (parent : (Frame.ofMountain mountain).Node),
      event = before + 1 ∧ previous ≤ before ∧ before < (Frame.ofMountain mountain).lastEvent ∧
      (Frame.ofMountain mountain).P
        (eventFrontier (build_normal_of_success hBuild).toOrdered before left) = some parent ∧
      (Frame.ofMountain mountain).P
        (eventFrontier (build_normal_of_success hBuild).toOrdered before right) = some parent := by
  cases event with
  | zero => omega
  | succ before =>
      have hNormal := build_normal_of_success hBuild
      have hCandidate := build_candidate_parent_at_first_difference hBuild hWidth hBound hLeftBound hRightBound
        (build_common_frontier_candidate_parent hBuild hWidth left right hLeftBound hRightBound hCommon)
        hStart hEvent hEarlier
      change eventParentMap hNormal.toOrdered hWidth bound before left.val =
        eventParentMap hNormal.toOrdered hWidth bound before right.val at hCandidate
      have hPrevCommon := hNormal.P_eq_of_eventParentMap_eq hWidth left right hLeftBound hRightBound hCandidate
      cases hp : (Frame.ofMountain mountain).P (eventFrontier hNormal.toOrdered before left) with
      | some parent => exact ⟨before, parent, rfl, by omega, by omega, hp, hPrevCommon.symm.trans hp⟩
      | none =>
          have hRightNone := hPrevCommon.symm.trans hp
          have hl := hNormal.eventFrontier_stable_of_parent_none (Nat.le_succ before) left hp
          have hr := hNormal.eventFrontier_stable_of_parent_none (Nat.le_succ before) right hRightNone
          have hLeftMap : eventParentMap hNormal.toOrdered hWidth bound (before + 1) left.val = none := by
            rw [hNormal.eventParentMap_at hWidth (before + 1) left hLeftBound, hl, hp]
            rfl
          have hRightMap : eventParentMap hNormal.toOrdered hWidth bound (before + 1) right.val = none := by
            rw [hNormal.eventParentMap_at hWidth (before + 1) right hRightBound, hr, hRightNone]
            rfl
          exact False.elim (hDifferent (by rw [parentDepth_none hLeftMap, parentDepth_none hRightMap]))

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.P_eq_of_eventParentMap_eq
#print axioms OmegaY.Geometry.Frame.Normal.eventFrontier_stable_of_parent_none
#print axioms OmegaY.Expansion.build_first_split_previous_parent
