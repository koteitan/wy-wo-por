/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/HighEventSuffix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.HighEventDepthWord

/-!
# Actual event samplings above any high common-upper threshold

A comparison starting above Z needs the suffix at its own common upper,
not an arbitrary restriction of a comparison beginning at Z. Actual high
row equality supplies the suffix sampling at every threshold at least Z.
-/

namespace OmegaY.Geometry.Frame

theorem highEventStart_eventCut (F : Frame) {event : Nat} (hEvent : event ≤ F.lastEvent) :
    F.highEventStart (F.eventCut event) = event := by
  have hLe := (F.highEventStart_le_iff (F.eventCut event) hEvent).mpr le_rfl
  apply Nat.le_antisymm hLe
  by_contra hn
  have hLess : F.highEventStart (F.eventCut event) < event := Nat.lt_of_not_ge hn
  cases event with
  | zero => omega
  | succ previous =>
      have hPrevious : previous ≤ F.lastEvent := by omega
      have hBack : F.eventCut (previous + 1) ≤ F.eventCut previous :=
        (F.highEventStart_le_iff (F.eventCut (previous + 1)) hPrevious).mp (by omega)
      exact (not_le_of_gt (F.eventCut_strict_step (by omega))) hBack

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

section Suffix

variable {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
  {copies : Nat} {result : Mountain}
  (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok result)
  {threshold : Row} (hThreshold : p.lastTop.row ≤ threshold)

include hLast hRun hThreshold in
theorem Preparation.blocks_eventCuts_above_eq :
    (Frame.ofMountain result).eventCuts.filter (fun row => decide (threshold ≤ row)) =
      (Frame.ofMountain p.reduced).eventCuts.filter (fun row => decide (threshold ≤ row)) := by
  apply ((Frame.ofMountain result).eventCuts_sorted.pairwise.filter _).eq_of_mem_iff
    ((Frame.ofMountain p.reduced).eventCuts_sorted.pairwise.filter _)
  intro row
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨(p.blocks_high_eventCuts_iff hLast hRun (hThreshold.trans h.2)).mp h.1, h.2⟩
  · intro h
    exact ⟨(p.blocks_high_eventCuts_iff hLast hRun (hThreshold.trans h.2)).mpr h.1, h.2⟩

noncomputable def Preparation.blocks_event_suffix_sampling :
    Forests.EventSampling ((Frame.ofMountain p.reduced).highEventStart threshold)
      (Frame.ofMountain p.reduced).lastEvent ((Frame.ofMountain result).highEventStart threshold)
      (Frame.ofMountain result).lastEvent :=
  highEventTailSampling (Frame.ofMountain p.reduced) (Frame.ofMountain result) threshold
    (p.blocks_eventCuts_above_eq hLast hRun hThreshold)

include hLast hRun hThreshold in
theorem Preparation.blocks_event_suffix_rows
    {event : Nat} (hStart : (Frame.ofMountain result).highEventStart threshold ≤ event)
    (hEnd : event ≤ (Frame.ofMountain result).lastEvent) :
    (Frame.ofMountain result).eventCut event =
      (Frame.ofMountain p.reduced).eventCut
        ((p.blocks_event_suffix_sampling hLast hRun hThreshold).sample event) :=
  highEventTailSampling_rows _ _ _ (p.blocks_eventCuts_above_eq hLast hRun hThreshold) hStart hEnd

variable (hTarget : (Frame.ofMountain result).Ordered)
  (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < result.size)
  (sourceInitial targetInitial : ParentMap)
  {sourceBound targetBound sourceColumn targetColumn : Nat}
  (hSourceBound : sourceBound < p.reduced.size) (hTargetBound : targetBound < result.size)
  (hSourceColumn : sourceColumn ≤ sourceBound) (hTargetColumn : targetColumn ≤ targetBound)
  (hDepth : HighCutDepthMatch (build_normal_of_success p.reduced_build).toOrdered hTarget
    hSourceWidth hTargetWidth p.lastTop.row sourceColumn targetColumn)

include hLast hRun hThreshold hSourceBound hTargetBound hSourceColumn hTargetColumn hDepth in
theorem Preparation.high_suffix_eventDepth_match
    {event : Nat} (hStart : (Frame.ofMountain result).highEventStart threshold ≤ event)
    (hEnd : event ≤ (Frame.ofMountain result).lastEvent) :
    Forests.eventDepth ((Frame.ofMountain result).frontierForests targetInitial
      (eventFrontierNat hTarget hTargetWidth) targetBound) event targetColumn =
    Forests.eventDepth ((Frame.ofMountain p.reduced).frontierForests sourceInitial
      (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth) sourceBound)
      ((p.blocks_event_suffix_sampling hLast hRun hThreshold).sample event) sourceColumn := by
  let sampling := p.blocks_event_suffix_sampling hLast hRun hThreshold
  have hBounds := sampling.bounds event hStart hEnd
  have hHigh := hThreshold.trans
    (((Frame.ofMountain p.reduced).highEventStart_le_iff threshold hBounds.2).mp hBounds.1)
  have hCut := p.blocks_event_suffix_rows hLast hRun hThreshold hStart hEnd
  have hTargetDepth := eventParentMap_depth_bound hTarget hTargetWidth hTargetBound hTargetColumn event
  have hSourceDepth := eventParentMap_depth_bound (build_normal_of_success p.reduced_build).toOrdered
    hSourceWidth hSourceBound hSourceColumn (sampling.sample event)
  exact hTargetDepth.trans ((hDepth (sampling.sample event) event hBounds.2 hEnd hHigh hCut).trans hSourceDepth.symm)

end Suffix

section Comparison

variable {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
  {copies : Nat} {result : Mountain}
  (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok result)
  {threshold : Row} (hThreshold : p.lastTop.row ≤ threshold)
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

include hLast hRun hThreshold hSourceBound hTargetBound hSourceLeft hSourceRight hTargetLeft hTargetRight
  hLeftDepth hRightDepth

/-- Word transport begins at the supplied high common-upper threshold.
The two pointwise matches remain explicit here; actual-copy modules supply
them from executions. In particular no lexicographic prefix is discarded. -/
theorem Preparation.high_suffix_word_comparison :
    let source := (Frame.ofMountain p.reduced).frontierForests sourceInitial
      (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth) sourceBound
    let target := (Frame.ofMountain result).frontierForests targetInitial
      (eventFrontierNat hTarget hTargetWidth) targetBound
    let sourceStart := (Frame.ofMountain p.reduced).highEventStart threshold
    let targetStart := (Frame.ofMountain result).highEventStart threshold
    (Forests.DepthWordEq target targetStart (Frame.ofMountain result).lastEvent targetLeft targetRight ↔
      Forests.DepthWordEq source sourceStart (Frame.ofMountain p.reduced).lastEvent sourceLeft sourceRight) ∧
    (Forests.DepthWordLt target targetStart (Frame.ofMountain result).lastEvent targetLeft targetRight ↔
      Forests.DepthWordLt source sourceStart (Frame.ofMountain p.reduced).lastEvent sourceLeft sourceRight) ∧
    (Forests.DepthWordLe target targetStart (Frame.ofMountain result).lastEvent targetLeft targetRight ↔
      Forests.DepthWordLe source sourceStart (Frame.ofMountain p.reduced).lastEvent sourceLeft sourceRight) := by
  dsimp only
  let sampling := p.blocks_event_suffix_sampling hLast hRun hThreshold
  have hLeft := fun event hStart hEnd => p.high_suffix_eventDepth_match hLast hRun hThreshold
    hTarget hSourceWidth hTargetWidth sourceInitial targetInitial hSourceBound hTargetBound
      hSourceLeft hTargetLeft hLeftDepth (event := event) hStart hEnd
  have hRight := fun event hStart hEnd => p.high_suffix_eventDepth_match hLast hRun hThreshold
    hTarget hSourceWidth hTargetWidth sourceInitial targetInitial hSourceBound hTargetBound
      hSourceRight hTargetRight hRightDepth (event := event) hStart hEnd
  exact ⟨sampling.zero_word_eq_iff hLeft hRight, sampling.zero_word_lt_iff hLeft hRight,
    sampling.zero_word_le_iff hLeft hRight⟩

end Comparison
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.highEventStart_eventCut
#print axioms OmegaY.Expansion.Preparation.blocks_eventCuts_above_eq
#print axioms OmegaY.Expansion.Preparation.blocks_event_suffix_sampling
#print axioms OmegaY.Expansion.Preparation.high_suffix_eventDepth_match
#print axioms OmegaY.Expansion.Preparation.high_suffix_word_comparison
