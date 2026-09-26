/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CutDepthWords.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowPathDepth
import OmegaY.Forests.DepthWordWitness

/-!
# Finite depth words strictly above a geometric cut

The next event after the actual floor of a cut is exactly the first event
strictly above that cut. This translates exhaustive cut-based comparison
proofs into the existing finite DepthWordEq and DepthWordLt definitions.
No inserted event or row index is silently discarded by the translation.
-/

namespace OmegaY.Geometry.Frame

structure EventCutFloor (F : Frame) (cut : Row) where
  event : Nat
  event_end : event ≤ F.lastEvent
  below : F.eventCut event ≤ cut
  maximal : ∀ row ∈ F.eventCuts, row ≤ cut → row ≤ F.eventCut event

theorem eventCutFloor_exists {F : Frame} (hF : F.Ordered) {cut : Row}
    (hCut : (1 : Row) ≤ cut) : Nonempty (EventCutFloor F cut) := by
  obtain ⟨event, hEnd, hBelow, hMaximal, _⟩ := event_floor_at_cut hF hCut
  exact ⟨⟨event, hEnd, hBelow, hMaximal⟩⟩

theorem EventCutFloor.next_le_of_cut_lt {F : Frame} {cut : Row}
    (floor : EventCutFloor F cut) {event : Nat} (hCut : cut < F.eventCut event) :
    floor.event + 1 ≤ event := by
  by_contra hn
  have hBelow := F.eventCut_monotone (show event ≤ floor.event by omega)
  exact (not_lt_of_ge (hBelow.trans floor.below)) hCut

theorem EventCutFloor.cut_lt_of_next_le {F : Frame} {cut : Row}
    (floor : EventCutFloor F cut) {event : Nat} (hNext : floor.event + 1 ≤ event)
    (hEnd : event ≤ F.lastEvent) : cut < F.eventCut event := by
  by_contra hn
  have hBound := floor.maximal _ (F.eventCut_mem event) (le_of_not_gt hn)
  have hStrict := F.eventCut_strict_step (show floor.event < F.lastEvent by omega)
  have hRows := F.eventCut_monotone hNext
  exact (not_lt_of_ge hBound) (hStrict.trans_le hRows)

theorem EventCutFloor.next_le_iff {F : Frame} {cut : Row}
    (floor : EventCutFloor F cut) {event : Nat} (hEnd : event ≤ F.lastEvent) :
    floor.event + 1 ≤ event ↔ cut < F.eventCut event :=
  ⟨fun h => floor.cut_lt_of_next_le h hEnd, floor.next_le_of_cut_lt⟩

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem EventCutFloor.depthWordEq_of_above_cut
    {F : Frame} {cut : Row} (floor : EventCutFloor F cut)
    (hF : F.Ordered) (hWidth : 0 < F.width) (bound left right : Nat)
    (hEqual : ∀ event, event ≤ F.lastEvent → cut < F.eventCut event →
      parentDepth (eventParentMap hF hWidth bound event) left =
        parentDepth (eventParentMap hF hWidth bound event) right) :
    Forests.DepthWordEq
      (F.frontierForests (bottomCandidateMap bound) (eventFrontierNat hF hWidth) bound)
      (floor.event + 1) F.lastEvent left right := by
  intro event hStart hEnd
  exact hEqual event hEnd (floor.cut_lt_of_next_le hStart hEnd)

theorem EventCutFloor.depthWordLt_of_above_cut
    {F : Frame} {cut : Row} (floor : EventCutFloor F cut)
    (hF : F.Ordered) (hWidth : 0 < F.width) (bound left right : Nat)
    {event : Nat} (hEnd : event ≤ F.lastEvent) (hCut : cut < F.eventCut event)
    (hEarlier : ∀ earlier, cut < F.eventCut earlier → earlier < event →
      parentDepth (eventParentMap hF hWidth bound earlier) left =
        parentDepth (eventParentMap hF hWidth bound earlier) right)
    (hStrict : parentDepth (eventParentMap hF hWidth bound event) left <
      parentDepth (eventParentMap hF hWidth bound event) right) :
    Forests.DepthWordLt
      (F.frontierForests (bottomCandidateMap bound) (eventFrontierNat hF hWidth) bound)
      (floor.event + 1) F.lastEvent left right := by
  refine ⟨event, floor.next_le_of_cut_lt hCut, hEnd, ?_, hStrict⟩
  intro earlier hStart hBefore
  exact hEarlier earlier (floor.cut_lt_of_next_le hStart (hBefore.le.trans hEnd)) hBefore

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.eventCutFloor_exists
#print axioms OmegaY.Geometry.Frame.EventCutFloor.next_le_of_cut_lt
#print axioms OmegaY.Geometry.Frame.EventCutFloor.cut_lt_of_next_le
#print axioms OmegaY.Geometry.Frame.EventCutFloor.next_le_iff
#print axioms OmegaY.Expansion.EventCutFloor.depthWordEq_of_above_cut
#print axioms OmegaY.Expansion.EventCutFloor.depthWordLt_of_above_cut
