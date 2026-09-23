/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/HighEventTailSampling.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighEventSampling
import OmegaY.Forests.SampledDepthWords

/-!
# Constant-offset sampling of the actual high event tails

The high tail of a strictly sorted event list is its suffix after all rows
below the threshold. Equal high tails thus yield a monotone, onto sampling
with a constant index offset. The statements include the empty-tail case:
then the start index is one beyond the final event and the sampling interval
is empty on both sides. No parent or depth comparison is asserted here.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem high_filter_eq_drop_low_length (rows : List Row)
    (hSorted : rows.Pairwise (· < ·)) (threshold : Row) :
    rows.filter (fun row => decide (threshold ≤ row)) =
      rows.drop (rows.filter (fun row => decide (row < threshold))).length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      obtain ⟨hHead, hTail⟩ := List.pairwise_cons.mp hSorted
      by_cases hLow : row < threshold
      · have hNotHigh : ¬ threshold ≤ row := not_le.mpr hLow
        simpa only [List.filter_cons, hLow, decide_true, hNotHigh, decide_false,
          Bool.false_eq_true, ↓reduceIte, List.length_cons, List.drop_succ_cons] using ih hTail
      · have hHigh : threshold ≤ row := le_of_not_gt hLow
        have hAll : ∀ other ∈ rows, threshold ≤ other :=
          fun other hOther => hHigh.trans (hHead other hOther).le
        have hLowEmpty : rows.filter (fun other => decide (other < threshold)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro other hOther
          simp only [not_lt_of_ge (hAll other hOther), decide_false, Bool.false_eq_true, not_false_eq_true]
        have hHighAll : rows.filter (fun other => decide (threshold ≤ other)) = rows := by
          apply List.filter_eq_self.mpr
          intro other hOther
          simp only [decide_eq_true_eq]
          exact hAll other hOther
        simp only [List.filter_cons, hLow, decide_false, hHigh, decide_true,
          Bool.false_eq_true, ↓reduceIte, hLowEmpty, List.length_nil, List.drop_zero, hHighAll]

end OmegaY.Expansion

namespace OmegaY.Geometry.Frame

/-- The first global event at or above the threshold, or the full event
count if no such event exists. -/
noncomputable def highEventStart (F : Frame) (threshold : Row) : Nat :=
  (F.eventCuts.filter (fun row => decide (row < threshold))).length

theorem highEventStart_le_length (F : Frame) (threshold : Row) :
    F.highEventStart threshold ≤ F.eventCuts.length := List.length_filter_le _ _

/-- High-event filtering selects a literal suffix of the actual event list. -/
theorem eventCuts_drop_highEventStart (F : Frame) (threshold : Row) :
    F.eventCuts.drop (F.highEventStart threshold) =
      F.eventCuts.filter (fun row => decide (threshold ≤ row)) :=
  (OmegaY.Expansion.high_filter_eq_drop_low_length F.eventCuts F.eventCuts_sorted.pairwise threshold).symm

/-- The high-tail index condition is equivalent to the actual cut's row
condition whenever the index is an actual event. -/
theorem highEventStart_le_iff (F : Frame) (threshold : Row) {event : Nat}
    (hEvent : event ≤ F.lastEvent) :
    F.highEventStart threshold ≤ event ↔ threshold ≤ F.eventCut event := by
  have hEventBound : event < F.eventCuts.length := hEvent.trans_lt F.lastEvent_lt
  rw [F.eventCut_of_lt hEventBound]
  constructor
  · intro hStart
    have hIn : F.eventCuts[event] ∈ F.eventCuts.drop (F.highEventStart threshold) := by
      apply List.mem_iff_getElem?.mpr
      refine ⟨event - F.highEventStart threshold, ?_⟩
      rw [List.getElem?_drop, Nat.add_sub_of_le hStart, List.getElem?_eq_getElem hEventBound]
    rw [F.eventCuts_drop_highEventStart] at hIn
    exact of_decide_eq_true (List.mem_filter.mp hIn).2
  · intro hHigh
    have hIn : F.eventCuts[event] ∈ F.eventCuts.filter (fun row => decide (threshold ≤ row)) :=
      List.mem_filter.mpr ⟨List.getElem_mem hEventBound, by simpa only [decide_eq_true_eq] using hHigh⟩
    rw [← F.eventCuts_drop_highEventStart] at hIn
    obtain ⟨index, hIndex, hRead⟩ := List.getElem_of_mem hIn
    have hIndexBound : F.highEventStart threshold + index < F.eventCuts.length := by
      simp only [List.length_drop] at hIndex
      omega
    have hRead' : F.eventCuts[F.highEventStart threshold + index] = F.eventCuts[event] := by
      simpa only [List.getElem_drop] using hRead
    have hEqual : (⟨F.highEventStart threshold + index, hIndexBound⟩ : Fin F.eventCuts.length) =
        ⟨event, hEventBound⟩ := F.eventCuts_sorted.strictMono_get.injective hRead'
    have hValues := congrArg Fin.val hEqual
    change F.highEventStart threshold + index = event at hValues
    omega

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- Equal actual high-event lists give the fixed-offset sampling of those
tails. Its range can be empty, so no existence of a high event is assumed. -/
noncomputable def highEventTailSampling (source target : Frame) (threshold : Row)
    (hRows : target.eventCuts.filter (fun row => decide (threshold ≤ row)) =
      source.eventCuts.filter (fun row => decide (threshold ≤ row))) :
    Forests.EventSampling (source.highEventStart threshold) source.lastEvent
      (target.highEventStart threshold) target.lastEvent := by
  have hDrop : target.eventCuts.drop (target.highEventStart threshold) =
      source.eventCuts.drop (source.highEventStart threshold) := by
    rw [target.eventCuts_drop_highEventStart, source.eventCuts_drop_highEventStart, hRows]
  have hLengths := congrArg List.length hDrop
  simp only [List.length_drop] at hLengths
  have hSourceStart := source.highEventStart_le_length threshold
  have hTargetStart := target.highEventStart_le_length threshold
  have hSourcePositive := source.eventCuts_length_pos
  have hTargetPositive := target.eventCuts_length_pos
  refine {
    sample := fun event => source.highEventStart threshold + (event - target.highEventStart threshold)
    bounds := ?_
    monotone := ?_
    covers := ?_ }
  · intro event hLower hUpper
    change event ≤ target.eventCuts.length - 1 at hUpper
    change source.highEventStart threshold ≤ _ ∧ _ ≤ source.eventCuts.length - 1
    omega
  · intro a b hLower hOrder hUpper
    omega
  · intro event hLower hUpper
    refine ⟨target.highEventStart threshold + (event - source.highEventStart threshold), ?_, ?_, ?_⟩
    · omega
    · change event ≤ source.eventCuts.length - 1 at hUpper
      change _ ≤ target.eventCuts.length - 1
      omega
    · omega

theorem highEventTailSampling_sample (source target : Frame) (threshold : Row)
    (hRows : target.eventCuts.filter (fun row => decide (threshold ≤ row)) =
      source.eventCuts.filter (fun row => decide (threshold ≤ row))) (event : Nat) :
    (highEventTailSampling source target threshold hRows).sample event =
      source.highEventStart threshold + (event - target.highEventStart threshold) := rfl

/-- The sampling agrees with the actual global event rows, not just the
relative offsets of two abstract intervals. -/
theorem highEventTailSampling_rows (source target : Frame) (threshold : Row)
    (hRows : target.eventCuts.filter (fun row => decide (threshold ≤ row)) =
      source.eventCuts.filter (fun row => decide (threshold ≤ row)))
    {event : Nat} (hStart : target.highEventStart threshold ≤ event) (hEnd : event ≤ target.lastEvent) :
    target.eventCut event =
      source.eventCut ((highEventTailSampling source target threshold hRows).sample event) := by
  have hDrop : target.eventCuts.drop (target.highEventStart threshold) =
      source.eventCuts.drop (source.highEventStart threshold) := by
    rw [target.eventCuts_drop_highEventStart, source.eventCuts_drop_highEventStart, hRows]
  have hTargetBound : event < target.eventCuts.length := hEnd.trans_lt target.lastEvent_lt
  have hBounds := (highEventTailSampling source target threshold hRows).bounds event hStart hEnd
  have hSourceBound : (highEventTailSampling source target threshold hRows).sample event <
      source.eventCuts.length := hBounds.2.trans_lt source.lastEvent_lt
  have hLookup := congrArg (fun rows : List Row => rows[event - target.highEventStart threshold]?) hDrop
  simp only [List.getElem?_drop] at hLookup
  have hTargetIndex : target.highEventStart threshold + (event - target.highEventStart threshold) = event :=
    Nat.add_sub_of_le hStart
  rw [hTargetIndex] at hLookup
  change target.eventCuts[event]? =
    source.eventCuts[(highEventTailSampling source target threshold hRows).sample event]? at hLookup
  rw [List.getElem?_eq_getElem hTargetBound, List.getElem?_eq_getElem hSourceBound] at hLookup
  rw [target.eventCut_of_lt hTargetBound, source.eventCut_of_lt hSourceBound]
  exact Option.some.inj hLookup

/-- The actual finite outer execution supplies the complete row equality
needed to construct a high-tail event sampling. -/
noncomputable def Preparation.blocks_high_event_sampling
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    Forests.EventSampling ((Frame.ofMountain p.reduced).highEventStart p.lastTop.row)
      (Frame.ofMountain p.reduced).lastEvent ((Frame.ofMountain result).highEventStart p.lastTop.row)
      (Frame.ofMountain result).lastEvent :=
  highEventTailSampling (Frame.ofMountain p.reduced) (Frame.ofMountain result) p.lastTop.row
    (p.blocks_high_eventCuts_eq hLast hRun)

theorem Preparation.blocks_high_event_sampling_rows
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {event : Nat} (hStart : (Frame.ofMountain result).highEventStart p.lastTop.row ≤ event)
    (hEnd : event ≤ (Frame.ofMountain result).lastEvent) :
    (Frame.ofMountain result).eventCut event =
      (Frame.ofMountain p.reduced).eventCut ((p.blocks_high_event_sampling hLast hRun).sample event) :=
  highEventTailSampling_rows _ _ _ (p.blocks_high_eventCuts_eq hLast hRun) hStart hEnd

/-- A source event known by its actual high cut automatically has a
corresponding target event, with the same row and the prescribed sampling
index. No target event is selected by the caller. -/
theorem Preparation.blocks_high_event_correspondence
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {sourceEvent : Nat} (hSourceEnd : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent) :
    ∃ targetEvent,
      (Frame.ofMountain result).highEventStart p.lastTop.row ≤ targetEvent ∧
      targetEvent ≤ (Frame.ofMountain result).lastEvent ∧
      (p.blocks_high_event_sampling hLast hRun).sample targetEvent = sourceEvent ∧
      (Frame.ofMountain result).eventCut targetEvent =
        (Frame.ofMountain p.reduced).eventCut sourceEvent := by
  have hSourceStart := ((Frame.ofMountain p.reduced).highEventStart_le_iff p.lastTop.row hSourceEnd).mpr hHigh
  obtain ⟨targetEvent, hStart, hEnd, hSample⟩ :=
    (p.blocks_high_event_sampling hLast hRun).covers sourceEvent hSourceStart hSourceEnd
  exact ⟨targetEvent, hStart, hEnd, hSample,
    by simpa only [hSample] using p.blocks_high_event_sampling_rows hLast hRun hStart hEnd⟩

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.eventCuts_drop_highEventStart
#print axioms OmegaY.Geometry.Frame.highEventStart_le_iff
#print axioms OmegaY.Expansion.highEventTailSampling
#print axioms OmegaY.Expansion.highEventTailSampling_rows
#print axioms OmegaY.Expansion.Preparation.blocks_high_event_sampling
#print axioms OmegaY.Expansion.Preparation.blocks_high_event_sampling_rows
#print axioms OmegaY.Expansion.Preparation.blocks_high_event_correspondence
