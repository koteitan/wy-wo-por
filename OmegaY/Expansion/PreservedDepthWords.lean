/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedDepthWords.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CutDepthWords
import OmegaY.Expansion.ActualLowRootPathDepth
import OmegaY.Expansion.HighEventDepthWord

/-!
# Complete depth words survive complete-column preservation

New columns can insert arbitrarily many actual events between retained
rows. Sampling each new event at the finite floor in the retained frame
is monotone and covers every old event. At any threshold which is an old
actual row, the complete words at or above that row agree, including all
the new repeated samples. No numerical-parent recognition is assumed.
-/

namespace OmegaY.Geometry.Frame

theorem eventCut_index_le {F : Frame} {a b : Nat} (ha : a ≤ F.lastEvent)
    (hRows : F.eventCut a ≤ F.eventCut b) : a ≤ b := by
  by_contra hn
  have hba : b < a := lt_of_not_ge hn
  have hStrict := (F.eventCut_strict_step (hba.trans_le ha)).trans_le
    (F.eventCut_monotone (show b + 1 ≤ a by omega))
  exact (not_lt_of_ge hRows) hStrict

theorem EventCutFloor.frontiers {F : Frame} {cut : Row}
    (floor : EventCutFloor F cut) (hF : F.Ordered) (hCut : (1 : Row) ≤ cut) :
    ∀ column, eventFrontier hF floor.event column = frontierAt hF cut hCut column := by
  intro column
  have hSpec := frontierAt_spec hF hCut column
  apply frontierAt_eq_of_upper_barrier hF (F.eventCut_one_le floor.event)
    (node := frontierAt hF cut hCut column)
  · exact floor.maximal _ (real_height_mem_eventCuts hF hSpec.2.1) hSpec.2.2.1
  · intro upper hUpper
    exact floor.below.trans_lt (hSpec.2.2.2.2 upper hUpper)

noncomputable def sampledEventFloor (F T : Frame) (hF : F.Ordered) (event : Nat) :
    EventCutFloor F (T.eventCut event) :=
  Classical.choice (eventCutFloor_exists hF (T.eventCut_one_le event))

theorem sampledEventFloor_monotone (F T : Frame) (hF : F.Ordered) :
    Monotone (fun event => (sampledEventFloor F T hF event).event) := by
  intro a b hab
  let fa := sampledEventFloor F T hF a
  let fb := sampledEventFloor F T hF b
  exact eventCut_index_le fa.event_end (fb.maximal _ (F.eventCut_mem fa.event)
    (fa.below.trans (T.eventCut_monotone hab)))

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

namespace PreservesColumns

variable {before after : Mountain} (preserved : PreservesColumns before after)
  (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
  (hSourceWidth : 0 < before.size) (hTargetWidth : 0 < after.size)
  {threshold : Row} (hThreshold : threshold ∈ (Frame.ofMountain before).eventCuts)

noncomputable def eventFloorSampling :
    Forests.EventSampling ((Frame.ofMountain before).highEventStart threshold)
      (Frame.ofMountain before).lastEvent ((Frame.ofMountain after).highEventStart threshold)
      (Frame.ofMountain after).lastEvent := by
  let F := Frame.ofMountain before
  let T := Frame.ofMountain after
  refine {
    sample := fun event => (sampledEventFloor F T hBefore event).event
    bounds := ?_
    monotone := fun a b _ hab _ => sampledEventFloor_monotone F T hBefore hab
    covers := ?_ }
  · intro event hStart hEnd
    let floor := sampledEventFloor F T hBefore event
    refine ⟨(F.highEventStart_le_iff threshold floor.event_end).mpr ?_, floor.event_end⟩
    exact floor.maximal _ hThreshold ((T.highEventStart_le_iff threshold hEnd).mp hStart)
  · intro event hStart hEnd
    obtain ⟨targetEvent, hTargetEnd, hRow⟩ := eventCut_of_member
      (mem_eventCuts.mpr (preserved.eventRows_subset (mem_eventCuts.mp (F.eventCut_mem event))))
    let floor := sampledEventFloor F T hBefore targetEvent
    have hFloorRow : F.eventCut floor.event = F.eventCut event := le_antisymm
      (floor.below.trans_eq hRow)
      (floor.maximal _ (F.eventCut_mem event) hRow.ge)
    have hFloorEq : floor.event = event := le_antisymm
      (eventCut_index_le floor.event_end hFloorRow.le)
      (eventCut_index_le hEnd hFloorRow.ge)
    refine ⟨targetEvent, (T.highEventStart_le_iff threshold hTargetEnd).mpr ?_, hTargetEnd, hFloorEq⟩
    exact ((F.highEventStart_le_iff threshold hEnd).mp hStart).trans_eq hRow.symm

include preserved in
theorem sampled_depth_eq {column : Nat} (hColumn : column < before.size) (event : Nat) :
    parentDepth (eventParentMap hAfter hTargetWidth (after.size - 1) event) column =
      parentDepth (eventParentMap hBefore hSourceWidth (before.size - 1)
        (sampledEventFloor (Frame.ofMountain before) (Frame.ofMountain after) hBefore event).event) column := by
  exact preserved.event_parentDepth_at_common_cut hBefore hAfter hSourceWidth hTargetWidth
    ((Frame.ofMountain after).eventCut_one_le event)
    ((sampledEventFloor (Frame.ofMountain before) (Frame.ofMountain after) hBefore event).frontiers
      hBefore ((Frame.ofMountain after).eventCut_one_le event))
    (fun _ => rfl) hColumn

include preserved hThreshold in
theorem depth_words_at_retained_row {left right : Nat}
    (hLeft : left < before.size) (hRight : right < before.size) :
    let F := Frame.ofMountain before
    let T := Frame.ofMountain after
    let sourceForests := F.frontierForests (bottomCandidateMap (before.size - 1))
      (eventFrontierNat hBefore hSourceWidth) (before.size - 1)
    let targetForests := T.frontierForests (bottomCandidateMap (after.size - 1))
      (eventFrontierNat hAfter hTargetWidth) (after.size - 1)
    (Forests.DepthWordEq targetForests (T.highEventStart threshold) T.lastEvent left right ↔
      Forests.DepthWordEq sourceForests (F.highEventStart threshold) F.lastEvent left right) ∧
    (Forests.DepthWordLt targetForests (T.highEventStart threshold) T.lastEvent left right ↔
      Forests.DepthWordLt sourceForests (F.highEventStart threshold) F.lastEvent left right) ∧
    (Forests.DepthWordLe targetForests (T.highEventStart threshold) T.lastEvent left right ↔
      Forests.DepthWordLe sourceForests (F.highEventStart threshold) F.lastEvent left right) := by
  let sampling := preserved.eventFloorSampling hBefore hThreshold
  have hL : ∀ event, (Frame.ofMountain after).highEventStart threshold ≤ event →
      event ≤ (Frame.ofMountain after).lastEvent →
      parentDepth (eventParentMap hAfter hTargetWidth (after.size - 1) event) left =
        parentDepth (eventParentMap hBefore hSourceWidth (before.size - 1) (sampling.sample event)) left :=
    fun event _ _ => preserved.sampled_depth_eq hBefore hAfter hSourceWidth hTargetWidth hLeft event
  have hR : ∀ event, (Frame.ofMountain after).highEventStart threshold ≤ event →
      event ≤ (Frame.ofMountain after).lastEvent →
      parentDepth (eventParentMap hAfter hTargetWidth (after.size - 1) event) right =
        parentDepth (eventParentMap hBefore hSourceWidth (before.size - 1) (sampling.sample event)) right :=
    fun event _ _ => preserved.sampled_depth_eq hBefore hAfter hSourceWidth hTargetWidth hRight event
  exact ⟨sampling.zero_word_eq_iff hL hR, sampling.zero_word_lt_iff hL hR,
    sampling.zero_word_le_iff hL hR⟩

end PreservesColumns
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.eventCut_index_le
#print axioms OmegaY.Geometry.Frame.EventCutFloor.frontiers
#print axioms OmegaY.Geometry.Frame.sampledEventFloor_monotone
#print axioms OmegaY.Expansion.PreservesColumns.eventFloorSampling
#print axioms OmegaY.Expansion.PreservesColumns.sampled_depth_eq
#print axioms OmegaY.Expansion.PreservesColumns.depth_words_at_retained_row
