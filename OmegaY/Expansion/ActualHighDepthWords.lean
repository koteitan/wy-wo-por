/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighDepthWords.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighCopiedDepth
import OmegaY.Expansion.HighEventDepthWord

/-!
# Actual high depth words

These interfaces instantiate the high-word converter from actual source
preservation and completed copying. No pointwise depth equality is an
input. The compared words start at the first event whose cut is at least
the old last top; no assertion about the preceding low events is made.

The copied/copy interface compares two columns in the same actual block.
The preserved/copy interface keeps the first column at its original
position. It does not identify a translated root with a block boundary.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- A compact spelling of equality and both order equivalences for the
full-column high-event depth words. Initial forests may be arbitrary:
the event-depth convention already selects the successor forest. -/
def HighDepthWordComparison {source target : Frame}
    (hSource : source.Ordered) (hTarget : target.Ordered)
    (hSourceWidth : 0 < source.width) (hTargetWidth : 0 < target.width)
    (threshold : Row) (sourceInitial targetInitial : ParentMap)
    (sourceLeft sourceRight targetLeft targetRight : Nat) : Prop :=
  let sourceForest := source.frontierForests sourceInitial
    (eventFrontierNat hSource hSourceWidth) (source.width - 1)
  let targetForest := target.frontierForests targetInitial
    (eventFrontierNat hTarget hTargetWidth) (target.width - 1)
  let sourceStart := source.highEventStart threshold
  let targetStart := target.highEventStart threshold
  (Forests.DepthWordEq targetForest targetStart target.lastEvent targetLeft targetRight ↔
    Forests.DepthWordEq sourceForest sourceStart source.lastEvent sourceLeft sourceRight) ∧
  (Forests.DepthWordLt targetForest targetStart target.lastEvent targetLeft targetRight ↔
    Forests.DepthWordLt sourceForest sourceStart source.lastEvent sourceLeft sourceRight) ∧
  (Forests.DepthWordLe targetForest targetStart target.lastEvent targetLeft targetRight ↔
    Forests.DepthWordLe sourceForest sourceStart source.lastEvent sourceLeft sourceRight)

section Matches

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block startCopies copies : Nat} {start ambient : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references p.reduced.size ambient)
  (history : CopyRunHistory p block start references p.reduced.size ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)
  (hAmbientRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok ambient)
  (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)

include history hLast hStartRun hAmbientRun

/-- Every actual copied right column supplies the converter's depth
identity; source and target frontiers are recovered inside the proof. -/
theorem DynamicBlockState.copied_high_cut_depth_match
    (sourceColumn : Fin (Frame.ofMountain p.reduced).width)
    (hRight : p.root.column < sourceColumn.val) :
    HighCutDepthMatch (build_normal_of_success p.reduced_build).toOrdered s.ambient_valid.toOrdered
      hSourceWidth hTargetWidth p.lastTop.row sourceColumn.val
      (sourceColumn.val + block * (p.reduced.size - 1 - p.root.column)) := by
  intro sourceEvent targetEvent hSourceEvent _ hHigh hCut
  exact s.actual_high_column_depth history hLast hStartRun hAmbientRun hSourceWidth hTargetWidth
    hRight hSourceEvent hHigh hCut

omit history hLast hStartRun hAmbientRun

/-- An original column retained in the actual ambient mountain supplies
the same-cut depth identity directly from complete-column preservation. -/
theorem DynamicBlockState.preserved_high_cut_depth_match
    (sourceColumn : Fin (Frame.ofMountain p.reduced).width) :
    HighCutDepthMatch (build_normal_of_success p.reduced_build).toOrdered s.ambient_valid.toOrdered
      hSourceWidth hTargetWidth p.lastTop.row sourceColumn.val sourceColumn.val := by
  intro sourceEvent targetEvent _ _ _ hCut
  exact s.base_ambient.event_parentDepth (build_normal_of_success p.reduced_build).toOrdered
    s.ambient_valid.toOrdered hSourceWidth hTargetWidth hCut sourceColumn.isLt

include s

private theorem DynamicBlockState.high_word_copied_bound
    (sourceColumn : Fin (Frame.ofMountain p.reduced).width) :
    sourceColumn.val + block * (p.reduced.size - 1 - p.root.column) ≤ ambient.size - 1 := by
  have hColumn : sourceColumn.val < p.reduced.size := sourceColumn.isLt
  have hSize := s.size_eq
  omega

private theorem DynamicBlockState.high_word_preserved_bound
    (sourceColumn : Fin (Frame.ofMountain p.reduced).width) :
    sourceColumn.val ≤ ambient.size - 1 := by
  have hColumn : sourceColumn.val < p.reduced.size := sourceColumn.isLt
  have hSize := s.size_eq
  omega

include history hLast hStartRun hAmbientRun

/-- The actual sampling certificate for two copied columns. Its four
correction functions are zero by construction. -/
noncomputable def DynamicBlockState.copied_high_word_correction
    (sourceInitial targetInitial : ParentMap)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeft : p.root.column < left.val) (hRight : p.root.column < right.val) :
    Forests.SampledDepthCorrection
      ((Frame.ofMountain p.reduced).frontierForests sourceInitial
        (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth)
        (p.reduced.size - 1))
      ((Frame.ofMountain ambient).frontierForests targetInitial
        (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) (ambient.size - 1))
      (p.blocks_high_event_sampling hLast hAmbientRun) left.val right.val
      (left.val + block * (p.reduced.size - 1 - p.root.column))
      (right.val + block * (p.reduced.size - 1 - p.root.column)) :=
  p.high_event_zero_correction hLast hAmbientRun s.ambient_valid.toOrdered hSourceWidth hTargetWidth
    sourceInitial targetInitial (sourceBound := p.reduced.size - 1) (targetBound := ambient.size - 1)
    (by omega) (by omega)
    (by have h : left.val < p.reduced.size := left.isLt; omega)
    (by have h : right.val < p.reduced.size := right.isLt; omega)
    (s.high_word_copied_bound left) (s.high_word_copied_bound right)
    (s.copied_high_cut_depth_match history hLast hStartRun hAmbientRun hSourceWidth hTargetWidth left hLeft)
    (s.copied_high_cut_depth_match history hLast hStartRun hAmbientRun hSourceWidth hTargetWidth right hRight)

/-- Equality, strict comparison and weak comparison are all equivalent
for the actual two copied columns throughout the high-event suffix. -/
theorem DynamicBlockState.copied_high_word_comparison
    (sourceInitial targetInitial : ParentMap)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeft : p.root.column < left.val) (hRight : p.root.column < right.val) :
    HighDepthWordComparison (build_normal_of_success p.reduced_build).toOrdered s.ambient_valid.toOrdered
      hSourceWidth hTargetWidth p.lastTop.row sourceInitial targetInitial left.val right.val
      (left.val + block * (p.reduced.size - 1 - p.root.column))
      (right.val + block * (p.reduced.size - 1 - p.root.column)) := by
  exact p.high_event_word_comparison hLast hAmbientRun s.ambient_valid.toOrdered hSourceWidth hTargetWidth
    sourceInitial targetInitial (sourceBound := p.reduced.size - 1) (targetBound := ambient.size - 1)
    (by omega) (by omega)
    (by have h : left.val < p.reduced.size := left.isLt; omega)
    (by have h : right.val < p.reduced.size := right.isLt; omega)
    (s.high_word_copied_bound left) (s.high_word_copied_bound right)
    (s.copied_high_cut_depth_match history hLast hStartRun hAmbientRun hSourceWidth hTargetWidth left hLeft)
    (s.copied_high_cut_depth_match history hLast hStartRun hAmbientRun hSourceWidth hTargetWidth right hRight)

/-- Mixed original/copy high words have the same zero correction. The
original endpoint can be any preserved source column. -/
noncomputable def DynamicBlockState.preserved_copied_high_word_correction
    (sourceInitial targetInitial : ParentMap)
    (preserved copied : Fin (Frame.ofMountain p.reduced).width)
    (hCopied : p.root.column < copied.val) :
    Forests.SampledDepthCorrection
      ((Frame.ofMountain p.reduced).frontierForests sourceInitial
        (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth)
        (p.reduced.size - 1))
      ((Frame.ofMountain ambient).frontierForests targetInitial
        (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) (ambient.size - 1))
      (p.blocks_high_event_sampling hLast hAmbientRun) preserved.val copied.val preserved.val
      (copied.val + block * (p.reduced.size - 1 - p.root.column)) :=
  p.high_event_zero_correction hLast hAmbientRun s.ambient_valid.toOrdered hSourceWidth hTargetWidth
    sourceInitial targetInitial (sourceBound := p.reduced.size - 1) (targetBound := ambient.size - 1)
    (by omega) (by omega)
    (by have h : preserved.val < p.reduced.size := preserved.isLt; omega)
    (by have h : copied.val < p.reduced.size := copied.isLt; omega)
    (s.high_word_preserved_bound preserved) (s.high_word_copied_bound copied)
    (s.preserved_high_cut_depth_match hSourceWidth hTargetWidth preserved)
    (s.copied_high_cut_depth_match history hLast hStartRun hAmbientRun hSourceWidth hTargetWidth copied hCopied)

/-- Actual mixed original/copy equality and both comparisons, with no
assumed target parent correspondence or target numerical normality. -/
theorem DynamicBlockState.preserved_copied_high_word_comparison
    (sourceInitial targetInitial : ParentMap)
    (preserved copied : Fin (Frame.ofMountain p.reduced).width)
    (hCopied : p.root.column < copied.val) :
    HighDepthWordComparison (build_normal_of_success p.reduced_build).toOrdered s.ambient_valid.toOrdered
      hSourceWidth hTargetWidth p.lastTop.row sourceInitial targetInitial preserved.val copied.val preserved.val
      (copied.val + block * (p.reduced.size - 1 - p.root.column)) := by
  exact p.high_event_word_comparison hLast hAmbientRun s.ambient_valid.toOrdered hSourceWidth hTargetWidth
    sourceInitial targetInitial (sourceBound := p.reduced.size - 1) (targetBound := ambient.size - 1)
    (by omega) (by omega)
    (by have h : preserved.val < p.reduced.size := preserved.isLt; omega)
    (by have h : copied.val < p.reduced.size := copied.isLt; omega)
    (s.high_word_preserved_bound preserved) (s.high_word_copied_bound copied)
    (s.preserved_high_cut_depth_match hSourceWidth hTargetWidth preserved)
    (s.copied_high_cut_depth_match history hLast hStartRun hAmbientRun hSourceWidth hTargetWidth copied hCopied)

end Matches
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.copied_high_cut_depth_match
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_high_cut_depth_match
#print axioms OmegaY.Expansion.DynamicBlockState.copied_high_word_correction
#print axioms OmegaY.Expansion.DynamicBlockState.copied_high_word_comparison
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_copied_high_word_correction
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_copied_high_word_comparison
