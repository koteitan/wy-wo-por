/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonParentEventTransition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentStepInterval
import OmegaY.Expansion.SourceFirstSplit
import OmegaY.Expansion.ActualContourEventOrder

/-! Source common-parent events either leave both nodes unchanged or
advance both through their actual uppers at the same global row. -/

namespace OmegaY.Geometry.Frame

theorem frontierAt_of_lower_cut {F : Frame} (hF : F.Ordered) {node : F.Node}
    {low high : Row} (hLow : (1 : Row) ≤ low) (hHigh : (1 : Row) ≤ high)
    (hFront : frontierAt hF high hHigh node.1 = node)
    (hBelow : F.height node ≤ low) (hOrder : low ≤ high) :
    frontierAt hF low hLow node.1 = node := by
  apply frontierAt_eq_of_upper_barrier hF hLow hBelow
  intro upper hUpper
  exact hOrder.trans_lt ((frontierAt_spec hF hHigh node.1).2.2.2.2 upper (hFront.symm ▸ hUpper))

theorem Normal.common_parent_move_or_stay {F : Frame} (hF : F.Normal)
    {event : Nat} (hEvent : event < F.lastEvent) (left right : Fin F.width)
    {parent : F.Node}
    (hLeft : F.P (eventFrontier hF.toOrdered event left) = some parent)
    (hRight : F.P (eventFrontier hF.toOrdered event right) = some parent) :
    (eventFrontier hF.toOrdered (event + 1) left = eventFrontier hF.toOrdered event left ∧
      eventFrontier hF.toOrdered (event + 1) right = eventFrontier hF.toOrdered event right) ∨
    (F.upper (eventFrontier hF.toOrdered event left) = some (eventFrontier hF.toOrdered (event + 1) left) ∧
      F.upper (eventFrontier hF.toOrdered event right) = some (eventFrontier hF.toOrdered (event + 1) right) ∧
      F.eventCut (event + 1) = F.height (eventFrontier hF.toOrdered (event + 1) left) ∧
      F.eventCut (event + 1) = F.height (eventFrontier hF.toOrdered (event + 1) right)) := by
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
  by_cases hStable : eventFrontier hF.toOrdered (event + 1) left = u
  · refine .inl ⟨hStable, ?_⟩
    have hNextBelow : F.eventCut (event + 1) < F.height uUpper :=
      (eventFrontier_spec hF.toOrdered (event + 1) left).2.2.2.2 uUpper (hStable.symm ▸ hUUpper)
    rw [← hz.1]
    apply frontierAt_eq_of_upper_barrier hF.toOrdered (F.eventCut_one_le (event + 1)) (node := z)
    · exact hz.2.2.1.trans (F.eventCut_monotone (Nat.le_succ event))
    · intro upper hUpper
      have he : zUpper = upper := Option.some.inj (hZUpper.symm.trans hUpper)
      exact he ▸ hNextBelow.trans_eq hRows
  · obtain ⟨hUAdvance, hNextCut⟩ := eventFrontier_advance hF.toOrdered hEvent left hStable
    have hUUpperEq : uUpper = eventFrontier hF.toOrdered (event + 1) left :=
      Option.some.inj (hUUpper.symm.trans hUAdvance)
    have hNextZCut : F.eventCut (event + 1) = F.height zUpper :=
      hNextCut.symm.trans ((congrArg F.height hUUpperEq).symm.trans hRows)
    have hZAt := (eventFrontier_pair_of_upper_cut hF.toOrdered hEvent hZUpper hNextZCut).2
    rw [hz.1] at hZAt
    exact .inr ⟨hUAdvance, hZUpper.trans (congrArg some hZAt.symm), hNextCut.symm,
      hNextZCut.trans (congrArg F.height hZAt.symm)⟩

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

theorem output_row_le_contourCut {cut : Row}
    (hBelow : (Frame.ofMountain p.reduced).height source ≤ cut) :
    copy.read.outputCell.row ≤ copy.contourCut cut := by
  rw [copy.read.output_row]
  exact Row.lift_monotone copy.read.source_lower hBelow

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.frontierAt_of_lower_cut
#print axioms OmegaY.Geometry.Frame.Normal.common_parent_move_or_stay
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.output_row_le_contourCut
