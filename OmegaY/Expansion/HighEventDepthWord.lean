/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/HighEventDepthWord.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.HighEventTailSampling
import OmegaY.Expansion.RawNumericSuffix

/-!
# Converting high-cut depth identities to sampled depth words

`eventDepth forests r` reads `forests (r + 1)`. For the actual
`frontierForests`, this is exactly `eventParentMap r`: the increment is
already absorbed, so the word's event index must not be shifted again.
Truncating a parent map beyond the compared column does not change depth.

This module is a converter. Its explicit `HighCutDepthMatch` inputs are
pointwise absolute-depth identities, which must be established separately
from actual copying. The real outer run supplies the high-event sampling;
it does not by itself discharge those depth inputs here.
-/

namespace OmegaY.Forests

open ZeroY

section ZeroCorrection

variable {source target : Nat → ParentMap}
  {sourceStart sourceFinish targetStart targetFinish : Nat}
  (sampling : EventSampling sourceStart sourceFinish targetStart targetFinish)
  {sourceLeft sourceRight targetLeft targetRight : Nat}
  (hLeft : ∀ t, targetStart ≤ t → t ≤ targetFinish →
    eventDepth target t targetLeft = eventDepth source (sampling.sample t) sourceLeft)
  (hRight : ∀ t, targetStart ≤ t → t ≤ targetFinish →
    eventDepth target t targetRight = eventDepth source (sampling.sample t) sourceRight)

/-- Pointwise equality is the zero-baseline, zero-extra special case. -/
def EventSampling.zeroCorrection :
    SampledDepthCorrection source target sampling sourceLeft sourceRight targetLeft targetRight where
  baseline := fun _ => 0
  extra := fun _ => 0
  leftCoefficient := fun _ => 0
  rightCoefficient := fun _ => 0
  left_balance := by intro t ht htf; simpa only [Nat.add_zero, Nat.zero_mul] using hLeft t ht htf
  right_balance := by intro t ht htf; simpa only [Nat.add_zero, Nat.zero_mul] using hRight t ht htf
  equal_coefficients := by intros; rfl
  ordered_coefficients := by intros; exact le_rfl

include sampling hLeft hRight

theorem EventSampling.zero_word_eq_iff :
    DepthWordEq target targetStart targetFinish targetLeft targetRight ↔
      DepthWordEq source sourceStart sourceFinish sourceLeft sourceRight := by
  constructor
  · intro hTarget s hs hsf
    obtain ⟨t, ht, htf, hSample⟩ := sampling.covers s hs hsf
    have he := (hLeft t ht htf).symm.trans ((hTarget t ht htf).trans (hRight t ht htf))
    simpa only [hSample] using he
  · exact (sampling.zeroCorrection hLeft hRight).word_eq

/-- Onto monotone sampling also reflects the first strict difference.
Repeated samples cannot hide an earlier source difference. -/
theorem EventSampling.zero_word_lt_iff :
    DepthWordLt target targetStart targetFinish targetLeft targetRight ↔
      DepthWordLt source sourceStart sourceFinish sourceLeft sourceRight := by
  constructor
  · rintro ⟨t, ht, htf, hEarlier, hLess⟩
    obtain ⟨hs, hsf⟩ := sampling.bounds t ht htf
    refine ⟨sampling.sample t, hs, hsf, ?_, ?_⟩
    · intro s hs hst
      obtain ⟨earlier, heStart, heEnd, heSample⟩ := sampling.covers s hs (hst.le.trans hsf)
      have heBefore : earlier < t := by
        by_contra hn
        have hMonotone := sampling.monotone t earlier ht (le_of_not_gt hn) heEnd
        rw [heSample] at hMonotone
        exact (not_lt_of_ge hMonotone) hst
      have he := (hLeft earlier heStart heEnd).symm.trans
        ((hEarlier earlier heStart heBefore).trans (hRight earlier heStart heEnd))
      simpa only [heSample] using he
    · simpa only [hLeft t ht htf, hRight t ht htf] using hLess
  · exact (sampling.zeroCorrection hLeft hRight).word_lt

theorem EventSampling.zero_word_le_iff :
    DepthWordLe target targetStart targetFinish targetLeft targetRight ↔
      DepthWordLe source sourceStart sourceFinish sourceLeft sourceRight :=
  or_congr (sampling.zero_word_eq_iff hLeft hRight) (sampling.zero_word_lt_iff hLeft hRight)

end ZeroCorrection
end OmegaY.Forests

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

/-- The actual event-depth convention has no extra shift: its internal
`r + 1` exactly selects `frontierParent ... r`. The initial map is irrelevant. -/
theorem eventDepth_frontierForests {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    (initial : ParentMap) (bound event column : Nat) :
    Forests.eventDepth (F.frontierForests initial (eventFrontierNat hF hWidth) bound) event column =
      parentDepth (eventParentMap hF hWidth bound event) column := rfl

/-- A cutoff beyond the current column leaves all visited parent edges
unchanged, so it leaves the full parent-chain depth unchanged. -/
theorem eventParentMap_depth_bound {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    {bound column : Nat} (hBound : bound < F.width) (hColumn : column ≤ bound) (event : Nat) :
    parentDepth (eventParentMap hF hWidth bound event) column =
      parentDepth (eventParentMap hF hWidth (F.width - 1) event) column := by
  apply parentDepth_congr_below (eventParentMap_leftward hF hWidth hBound event)
  intro i hi
  have hSmall : i ≤ bound := hi.trans hColumn
  have hFull : i ≤ F.width - 1 := by omega
  simp only [eventParentMap, frontierParent, if_pos hSmall, if_pos hFull]

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- A clearly isolated pointwise input for the converter: at any actual
same-row high events, the indicated target and source absolute depths agree.
It asserts neither a word comparison nor a correction certificate. -/
def HighCutDepthMatch {source target : Frame} (hSource : source.Ordered) (hTarget : target.Ordered)
    (hSourceWidth : 0 < source.width) (hTargetWidth : 0 < target.width)
    (threshold : Row) (sourceColumn targetColumn : Nat) : Prop :=
  ∀ sourceEvent targetEvent, sourceEvent ≤ source.lastEvent → targetEvent ≤ target.lastEvent →
    threshold ≤ source.eventCut sourceEvent → target.eventCut targetEvent = source.eventCut sourceEvent →
    parentDepth (eventParentMap hTarget hTargetWidth (target.width - 1) targetEvent) targetColumn =
      parentDepth (eventParentMap hSource hSourceWidth (source.width - 1) sourceEvent) sourceColumn

/-- The actual high sampling and a same-cut depth identity give the
correctly indexed depth equality for arbitrary valid prefix cutoffs. -/
theorem Preparation.high_eventDepth_match
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    (hTarget : (Frame.ofMountain result).Ordered)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < result.size)
    (sourceInitial targetInitial : ParentMap)
    {sourceBound targetBound sourceColumn targetColumn : Nat}
    (hSourceBound : sourceBound < p.reduced.size) (hTargetBound : targetBound < result.size)
    (hSourceColumn : sourceColumn ≤ sourceBound) (hTargetColumn : targetColumn ≤ targetBound)
    (hDepth : HighCutDepthMatch (build_normal_of_success p.reduced_build).toOrdered hTarget
      hSourceWidth hTargetWidth p.lastTop.row sourceColumn targetColumn)
    {event : Nat} (hStart : (Frame.ofMountain result).highEventStart p.lastTop.row ≤ event)
    (hEnd : event ≤ (Frame.ofMountain result).lastEvent) :
    Forests.eventDepth ((Frame.ofMountain result).frontierForests targetInitial
      (eventFrontierNat hTarget hTargetWidth) targetBound) event targetColumn =
    Forests.eventDepth ((Frame.ofMountain p.reduced).frontierForests sourceInitial
      (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth) sourceBound)
      ((p.blocks_high_event_sampling hLast hRun).sample event) sourceColumn := by
  let sampling := p.blocks_high_event_sampling hLast hRun
  have hBounds := sampling.bounds event hStart hEnd
  have hHigh := ((Frame.ofMountain p.reduced).highEventStart_le_iff p.lastTop.row hBounds.2).mp hBounds.1
  have hCut := p.blocks_high_event_sampling_rows hLast hRun hStart hEnd
  have hTargetDepth := eventParentMap_depth_bound hTarget hTargetWidth hTargetBound hTargetColumn event
  have hSourceDepth := eventParentMap_depth_bound (build_normal_of_success p.reduced_build).toOrdered
    hSourceWidth hSourceBound hSourceColumn (sampling.sample event)
  exact hTargetDepth.trans ((hDepth (sampling.sample event) event hBounds.2 hEnd hHigh hCut).trans hSourceDepth.symm)

section ActualConverter

variable {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
  {copies : Nat} {result : Mountain}
  (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok result)
  (hTarget : (Frame.ofMountain result).Ordered)
  (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < result.size)
  (sourceInitial targetInitial : ParentMap)
  {sourceBound targetBound sourceLeft sourceRight targetLeft targetRight : Nat}
  (hSourceBound : sourceBound < p.reduced.size) (hTargetBound : targetBound < result.size)
  (hSourceLeft : sourceLeft ≤ sourceBound) (hSourceRight : sourceRight ≤ sourceBound)
  (hTargetLeft : targetLeft ≤ targetBound) (hTargetRight : targetRight ≤ targetBound)
  (hLeftDepth : HighCutDepthMatch (build_normal_of_success p.reduced_build).toOrdered hTarget
    hSourceWidth hTargetWidth p.lastTop.row sourceLeft targetLeft)
  (hRightDepth : HighCutDepthMatch (build_normal_of_success p.reduced_build).toOrdered hTarget
    hSourceWidth hTargetWidth p.lastTop.row sourceRight targetRight)

/-- This constructor leaves its two pointwise depth inputs explicit. All
four numerical correction functions are identically zero. -/
noncomputable def Preparation.high_event_zero_correction :
    Forests.SampledDepthCorrection
      ((Frame.ofMountain p.reduced).frontierForests sourceInitial
        (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth) sourceBound)
      ((Frame.ofMountain result).frontierForests targetInitial (eventFrontierNat hTarget hTargetWidth) targetBound)
      (p.blocks_high_event_sampling hLast hRun) sourceLeft sourceRight targetLeft targetRight :=
  (p.blocks_high_event_sampling hLast hRun).zeroCorrection
    (fun _ hStart hEnd => p.high_eventDepth_match hLast hRun hTarget hSourceWidth hTargetWidth
      sourceInitial targetInitial hSourceBound hTargetBound hSourceLeft hTargetLeft hLeftDepth hStart hEnd)
    (fun _ hStart hEnd => p.high_eventDepth_match hLast hRun hTarget hSourceWidth hTargetWidth
      sourceInitial targetInitial hSourceBound hTargetBound hSourceRight hTargetRight hRightDepth hStart hEnd)

include hLast hRun hSourceBound hTargetBound hSourceLeft hSourceRight hTargetLeft hTargetRight
  hLeftDepth hRightDepth

/-- Equality and both lexicographic comparisons of the finite high depth
words are equivalent under actual sampling and the explicit depth inputs.
There is no extra shift of the event intervals. -/
theorem Preparation.high_event_word_comparison :
    let source := (Frame.ofMountain p.reduced).frontierForests sourceInitial
      (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth) sourceBound
    let target := (Frame.ofMountain result).frontierForests targetInitial
      (eventFrontierNat hTarget hTargetWidth) targetBound
    let sourceStart := (Frame.ofMountain p.reduced).highEventStart p.lastTop.row
    let targetStart := (Frame.ofMountain result).highEventStart p.lastTop.row
    (Forests.DepthWordEq target targetStart (Frame.ofMountain result).lastEvent targetLeft targetRight ↔
      Forests.DepthWordEq source sourceStart (Frame.ofMountain p.reduced).lastEvent sourceLeft sourceRight) ∧
    (Forests.DepthWordLt target targetStart (Frame.ofMountain result).lastEvent targetLeft targetRight ↔
      Forests.DepthWordLt source sourceStart (Frame.ofMountain p.reduced).lastEvent sourceLeft sourceRight) ∧
    (Forests.DepthWordLe target targetStart (Frame.ofMountain result).lastEvent targetLeft targetRight ↔
      Forests.DepthWordLe source sourceStart (Frame.ofMountain p.reduced).lastEvent sourceLeft sourceRight) := by
  dsimp only
  let sampling := p.blocks_high_event_sampling hLast hRun
  have hLeft := fun event hStart hEnd => p.high_eventDepth_match hLast hRun hTarget hSourceWidth hTargetWidth
    sourceInitial targetInitial hSourceBound hTargetBound hSourceLeft hTargetLeft hLeftDepth
      (event := event) hStart hEnd
  have hRight := fun event hStart hEnd => p.high_eventDepth_match hLast hRun hTarget hSourceWidth hTargetWidth
    sourceInitial targetInitial hSourceBound hTargetBound hSourceRight hTargetRight hRightDepth
      (event := event) hStart hEnd
  exact ⟨sampling.zero_word_eq_iff hLeft hRight, sampling.zero_word_lt_iff hLeft hRight,
    sampling.zero_word_le_iff hLeft hRight⟩

end ActualConverter
end OmegaY.Expansion

#print axioms OmegaY.Forests.EventSampling.zero_word_lt_iff
#print axioms OmegaY.Geometry.Frame.eventDepth_frontierForests
#print axioms OmegaY.Geometry.Frame.eventParentMap_depth_bound
#print axioms OmegaY.Expansion.Preparation.high_eventDepth_match
#print axioms OmegaY.Expansion.Preparation.high_event_zero_correction
#print axioms OmegaY.Expansion.Preparation.high_event_word_comparison
