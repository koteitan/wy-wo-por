/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSplitEvent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentAdvance

/-!+# Shared actual event in an unmarked first-split step

If source frontiers have the same designated parent before an event and
different designated depths afterwards, both frontiers actually move to
their immediate uppers. The real copied event is then supplied by their
executed unmarked contour advances. The new designated parents need not
agree. Marker transitions remain a separate branch.
-/

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

theorem Normal.common_parent_split_step {F : Frame} (hF : F.Normal)
    {event : Nat} (hEvent : event < F.lastEvent) (left right : Fin F.width)
    {parent : F.Node}
    (hLeft : F.P (eventFrontier hF.toOrdered event left) = some parent)
    (hRight : F.P (eventFrontier hF.toOrdered event right) = some parent)
    (hDifferent : F.P (eventFrontier hF.toOrdered (event + 1) left) ≠
      F.P (eventFrontier hF.toOrdered (event + 1) right)) :
    F.upper (eventFrontier hF.toOrdered event left) =
        some (eventFrontier hF.toOrdered (event + 1) left) ∧
      F.upper (eventFrontier hF.toOrdered event right) =
        some (eventFrontier hF.toOrdered (event + 1) right) := by
  let u := eventFrontier hF.toOrdered event left
  let z := eventFrontier hF.toOrdered event right
  obtain ⟨uUpper, hUUpper⟩ := hF.upper_of_parent hLeft
  obtain ⟨zUpper, hZUpper⟩ := hF.upper_of_parent hRight
  have hu := eventFrontier_spec hF.toOrdered event left
  have hz := eventFrontier_spec hF.toOrdered event right
  have hRows : F.height uUpper = F.height zUpper := by
    rcases le_total (F.height z) (F.height u) with hle | hle
    · exact hF.common_parent_upper_rows hLeft hRight hUUpper hZUpper hle
        (hu.2.2.1.trans_lt (hz.2.2.2.2 zUpper hZUpper))
    · exact (hF.common_parent_upper_rows hRight hLeft hZUpper hUUpper hle
        (hz.2.2.1.trans_lt (hu.2.2.2.2 uUpper hUUpper))).symm
  have hUChanged : eventFrontier hF.toOrdered (event + 1) left ≠ u := by
    intro hStable
    have hNextBelow : F.eventCut (event + 1) < F.height uUpper :=
      (eventFrontier_spec hF.toOrdered (event + 1) left).2.2.2.2 uUpper
        (hStable.symm ▸ hUUpper)
    have hZStable : eventFrontier hF.toOrdered (event + 1) right = z := by
      rw [← hz.1]
      apply frontierAt_eq_of_upper_barrier hF.toOrdered (F.eventCut_one_le (event + 1)) (node := z)
      · exact hz.2.2.1.trans (F.eventCut_monotone (Nat.le_succ event))
      · intro upper hUpper
        have he : zUpper = upper := Option.some.inj (hZUpper.symm.trans hUpper)
        exact he ▸ hNextBelow.trans_eq hRows
    exact hDifferent (by rw [hStable, hZStable]; exact hLeft.trans hRight.symm)
  obtain ⟨hUAdvance, hNextCut⟩ := eventFrontier_advance hF.toOrdered hEvent left hUChanged
  have hUUpperEq : uUpper = eventFrontier hF.toOrdered (event + 1) left :=
    Option.some.inj (hUUpper.symm.trans hUAdvance)
  have hNextZCut : F.eventCut (event + 1) = F.height zUpper :=
    hNextCut.symm.trans ((congrArg F.height hUUpperEq).symm.trans hRows)
  have hZAt := (eventFrontier_pair_of_upper_cut hF.toOrdered hEvent hZUpper hNextZCut).2
  rw [hz.1] at hZAt
  exact ⟨hUAdvance, hZUpper.trans (congrArg some hZAt.symm)⟩

/-- In one actual event forest, equal designated parents force equal
depths. This supplies genuine source motion from a strict depth difference,
rather than taking the motion or the source adjacency as an oracle. -/
theorem Normal.common_parent_depth_split_step {F : Frame} (hF : F.Normal)
    (hWidth : 0 < F.width) {bound event : Nat} (hBound : bound < F.width)
    (hEvent : event < F.lastEvent) (left right : Fin F.width)
    (hLeftBound : left.val ≤ bound) (hRightBound : right.val ≤ bound)
    {parent : F.Node}
    (hLeft : F.P (eventFrontier hF.toOrdered event left) = some parent)
    (hRight : F.P (eventFrontier hF.toOrdered event right) = some parent)
    (hDifferent : parentDepth (eventParentMap hF.toOrdered hWidth bound (event + 1)) left.val ≠
      parentDepth (eventParentMap hF.toOrdered hWidth bound (event + 1)) right.val) :
    F.upper (eventFrontier hF.toOrdered event left) =
        some (eventFrontier hF.toOrdered (event + 1) left) ∧
      F.upper (eventFrontier hF.toOrdered event right) =
        some (eventFrontier hF.toOrdered (event + 1) right) := by
  apply hF.common_parent_split_step hEvent left right hLeft hRight
  intro hSame
  let parentMap := eventParentMap hF.toOrdered hWidth bound (event + 1)
  have hLeftward : Leftward parentMap := eventParentMap_leftward hF.toOrdered hWidth hBound (event + 1)
  have hMaps : parentMap left.val = parentMap right.val := by
    dsimp only [parentMap]
    rw [hF.eventParentMap_at hWidth (event + 1) left hLeftBound,
      hF.eventParentMap_at hWidth (event + 1) right hRightBound, hSame]
  apply hDifferent
  change parentDepth parentMap left.val = parentDepth parentMap right.val
  cases hm : parentMap left.val with
  | none => rw [parentDepth_none hm, parentDepth_none (hMaps.symm.trans hm)]
  | some father => rw [parentDepth_some hLeftward hm, parentDepth_some hLeftward (hMaps.symm.trans hm)]

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- At an actual source depth split, four executed unmarked occurrences
determine a shared target event. The next source parents are allowed to
differ, and no target cut, target adjacency or target numerical P is input. -/
theorem actual_unmarked_split_event
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    (hLast : 1 < last) (hValid : MountainValid result)
    (hWidth : 0 < p.reduced.size) {bound event : Nat} (hBound : bound < p.reduced.size)
    (hEvent : event < (Frame.ofMountain p.reduced).lastEvent)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBound : left.val ≤ bound) (hRightBound : right.val ≤ bound)
    (uCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) result)
    (zCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) result)
    (nextUCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) left) result)
    (nextZCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) right) result)
    (hUUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left).2.val ∉
      (p.marked[left.val]?.getD []).map Ref.index)
    (hZUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right).2.val ∉
      (p.marked[right.val]?.getD []).map Ref.index)
    (hNextUUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) left).2.val ∉
      (p.marked[left.val]?.getD []).map Ref.index)
    (hNextZUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) right).2.val ∉
      (p.marked[right.val]?.getD []).map Ref.index)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hLeft : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) = some parent)
    (hRight : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) = some parent)
    (hDifferent : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hWidth bound (event + 1)) left.val ≠
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hWidth bound (event + 1)) right.val) :
    ∃ (actualU actualZ : (Frame.ofMountain result).Node) (targetEvent : Nat),
      Frame.ref actualU = nextUCopy.outputRef ∧ Frame.ref actualZ = nextZCopy.outputRef ∧
      (Frame.ofMountain result).cell actualU = nextUCopy.read.outputCell ∧
      (Frame.ofMountain result).cell actualZ = nextZCopy.read.outputCell ∧
      (Frame.ofMountain result).height actualU = (Frame.ofMountain result).height actualZ ∧
      targetEvent ≤ (Frame.ofMountain result).lastEvent ∧
      (Frame.ofMountain result).eventCut targetEvent = (Frame.ofMountain result).height actualU ∧
      eventFrontier hValid.toOrdered targetEvent actualU.1 = actualU ∧
      eventFrontier hValid.toOrdered targetEvent actualZ.1 = actualZ := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨hUUpper, hZUpper⟩ := hNormal.common_parent_depth_split_step hWidth hBound hEvent left right
    hLeftBound hRightBound hLeft hRight hDifferent
  have hu := (eventFrontier_spec hNormal.toOrdered event left).1
  have hz := (eventFrontier_spec hNormal.toOrdered event right).1
  have hnu := (eventFrontier_spec hNormal.toOrdered (event + 1) left).1
  have hnz := (eventFrontier_spec hNormal.toOrdered (event + 1) right).1
  exact common_parent_advance_event uCopy zCopy nextUCopy nextZCopy hLast hValid
    (by simpa only [hu] using hUUnmarked) (by simpa only [hz] using hZUnmarked)
    (by simpa only [hnu] using hNextUUnmarked) (by simpa only [hnz] using hNextZUnmarked)
    hLeft hRight hUUpper hZUpper ((Frame.ofMountain p.reduced).eventCut_one_le event)
    (by rw [hu]; rfl) (by rw [hz]; rfl)

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.common_parent_split_step
#print axioms OmegaY.Geometry.Frame.Normal.common_parent_depth_split_step
#print axioms OmegaY.Expansion.actual_unmarked_split_event
