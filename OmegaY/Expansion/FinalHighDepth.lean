/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinalHighDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualIteratedHighDepth
import OmegaY.Expansion.FinalHighEventSampling

/-!
# High-event depths in the actual returned expansion

For positive copy counts the program returns the completed blocks with
their final column removed. Complete-prefix preservation transfers the
proved event depths to every surviving column, using equal actual cuts
instead of assuming unchanged event indices. The deleted column is
explicitly excluded. The program's separate zero-copy return is not used.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- Actual `expandDiagram` returns the same high-cut depth on every
surviving block/source column. The survival bound prevents a removed or
out-of-range column from being interpreted through the map's default. -/
theorem Preparation.expandDiagram_high_depth_at_equal_cut
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hValid : MountainValid result) (hSourceWidth : 0 < p.reduced.size)
    (hTargetWidth : 0 < result.size)
    {block : Nat} (hBlock : block ≤ copies)
    {sourceColumn : Fin (Frame.ofMountain p.reduced).width}
    (hRight : p.root.column < sourceColumn.val)
    {sourceEvent targetEvent : Nat}
    (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hCut : (Frame.ofMountain result).eventCut targetEvent =
      (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hSurvives : sourceColumn.val + block * (p.reduced.size - 1 - p.root.column) < result.size) :
    parentDepth (eventParentMap hValid.toOrdered hTargetWidth (result.size - 1) targetEvent)
        (sourceColumn.val + block * (p.reduced.size - 1 - p.root.column)) =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) sourceColumn.val := by
  obtain ⟨full, hFull, ready⟩ := p.blocks_total hLast copies
  have he : full.pop = result := Except.ok.inj
    ((p.expandDiagram_of_blocks hLast hCopies hFull).symm.trans hRun)
  have hPreserved : PreservesColumns result full := he ▸ PreservesColumns.pop_prefix full
  have hFullWidth : 0 < full.size := hSourceWidth.trans_le ready.base_preserved.size_le
  obtain ⟨fullEvent, _, _, _, hFullCut⟩ :=
    p.blocks_high_event_correspondence hLast hFull hSourceEvent hHigh
  have hFullDepth := p.blocks_high_depth_at_equal_cut hLast hFull ready.valid
    hSourceWidth hFullWidth hBlock hRight hSourceEvent hHigh hFullCut
  have hSame := hPreserved.event_parentDepth hValid.toOrdered ready.valid.toOrdered
    hTargetWidth hFullWidth (hFullCut.trans hCut.symm) hSurvives
  exact hSame.symm.trans hFullDepth

/-- The exact high-event sampling of the returned expansion chooses one
target event for all surviving block columns. No target event or depth
correspondence is an input. -/
theorem Preparation.expandDiagram_all_high_depth
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent) :
    ∃ (hValid : MountainValid result) (hSourceWidth : 0 < p.reduced.size)
      (hTargetWidth : 0 < result.size) (targetEvent : Nat),
      (Frame.ofMountain result).highEventStart p.lastTop.row ≤ targetEvent ∧
      targetEvent ≤ (Frame.ofMountain result).lastEvent ∧
      (p.expandDiagram_high_event_sampling hLast hCopies hRun).sample targetEvent = sourceEvent ∧
      (Frame.ofMountain result).eventCut targetEvent =
        (Frame.ofMountain p.reduced).eventCut sourceEvent ∧
      ∀ block, block ≤ copies → ∀ sourceColumn : Fin (Frame.ofMountain p.reduced).width,
        p.root.column < sourceColumn.val →
        sourceColumn.val + block * (p.reduced.size - 1 - p.root.column) < result.size →
        parentDepth (eventParentMap hValid.toOrdered hTargetWidth (result.size - 1) targetEvent)
            (sourceColumn.val + block * (p.reduced.size - 1 - p.root.column)) =
          parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
            (p.reduced.size - 1) sourceEvent) sourceColumn.val := by
  obtain ⟨full, hFull, ready⟩ := p.blocks_total hLast copies
  have he : full.pop = result := Except.ok.inj
    ((p.expandDiagram_of_blocks hLast hCopies hFull).symm.trans hRun)
  have hValid : MountainValid result := he ▸ ready.valid.pop
  have hPreserved := p.expandDiagram_reduced_preserved hLast hCopies hRun
  obtain ⟨nodes, hNodes, _⟩ := cellAt_ok_iff.mp p.restored_root
  have hRootBound := (Array.getElem?_eq_some_iff.mp hNodes).1
  have hSourceWidth : 0 < p.reduced.size := (Nat.zero_le p.root.column).trans_lt hRootBound
  have hTargetWidth : 0 < result.size := hSourceWidth.trans_le hPreserved.size_le
  have hSourceStart := ((Frame.ofMountain p.reduced).highEventStart_le_iff p.lastTop.row hSourceEvent).mpr hHigh
  obtain ⟨targetEvent, hStart, hEnd, hSample⟩ :=
    (p.expandDiagram_high_event_sampling hLast hCopies hRun).covers sourceEvent hSourceStart hSourceEvent
  have hCut : (Frame.ofMountain result).eventCut targetEvent =
      (Frame.ofMountain p.reduced).eventCut sourceEvent := by
    simpa only [hSample] using p.expandDiagram_high_event_sampling_rows hLast hCopies hRun hStart hEnd
  refine ⟨hValid, hSourceWidth, hTargetWidth, targetEvent, hStart, hEnd, hSample, hCut, ?_⟩
  intro block hBlock sourceColumn hRight hSurvives
  exact p.expandDiagram_high_depth_at_equal_cut hLast hCopies hRun hValid hSourceWidth hTargetWidth
    hBlock hRight hSourceEvent hHigh hCut hSurvives

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.expandDiagram_high_depth_at_equal_cut
#print axioms OmegaY.Expansion.Preparation.expandDiagram_all_high_depth
