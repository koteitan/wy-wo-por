/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinalHighEventSampling.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.HighEventTailSampling
import OmegaY.Expansion.HistoryPrefix
import OmegaY.Expansion.TruncateValues

/-!
# High-event correspondence for the actual returned expansion

With a positive copy count the last pop leaves the whole reduced source
as a complete prefix. Every surviving high row also came from that source,
so the exact high event list and its constant-offset sampling survive the
actual truncation. The zero-copy branch has a different return expression
and is deliberately excluded from this source-prefix assertion.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem PreservesColumns.pop_prefix (mountain : Mountain) :
    PreservesColumns mountain.pop mountain := by
  intro column hColumn
  have hBefore : column < mountain.size - 1 := by simpa only [Array.size_pop] using hColumn
  simp only [Array.getElem?_pop, hBefore, ↓reduceIte]

theorem PreservesColumns.pop_of_size {before after : Mountain}
    (h : PreservesColumns before after) (hSize : before.size ≤ after.size - 1) :
    PreservesColumns before after.pop :=
  h.between_prefixes (PreservesColumns.pop_prefix after) (by simpa only [Array.size_pop] using hSize)

theorem Preparation.expandDiagram_reduced_preserved
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    PreservesColumns p.reduced result := by
  obtain ⟨full, hFull, ready⟩ := p.blocks_total hLast copies
  have he : full.pop = result := Except.ok.inj
    ((p.expandDiagram_of_blocks hLast hCopies hFull).symm.trans hRun)
  subst result
  have hSourceSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSourceSize
  have hWidth : 0 < p.reduced.size - 1 - p.root.column := by
    have hRoot := p.root_before_last
    omega
  have hPositive := Nat.mul_pos hCopies hWidth
  have hInitial := (p.initial_block_ready hLast).size_eq
  have hFinal := ready.size_eq
  simp only [Nat.add_mul, Nat.one_mul] at hInitial hFinal
  exact ready.base_preserved.pop_of_size (by omega)

theorem Preparation.expandDiagram_high_eventCuts_iff
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {row : Row} (hHigh : p.lastTop.row ≤ row) :
    row ∈ (Frame.ofMountain result).eventCuts ↔ row ∈ (Frame.ofMountain p.reduced).eventCuts := by
  have hPreserved := p.expandDiagram_reduced_preserved hLast hCopies hRun
  obtain ⟨full, hFull, _⟩ := p.blocks_total hLast copies
  have he : full.pop = result := Except.ok.inj
    ((p.expandDiagram_of_blocks hLast hCopies hFull).symm.trans hRun)
  constructor
  · intro hRow
    have hInResult : row ∈ (Frame.ofMountain result).eventRows := Frame.mem_eventCuts.mp hRow
    have hInFull : row ∈ (Frame.ofMountain full).eventRows :=
      (PreservesColumns.pop_prefix full).eventRows_subset (he ▸ hInResult)
    exact Frame.mem_eventCuts.mpr ((p.blocks_high_eventRows_iff hLast hFull hHigh).mp hInFull)
  · intro hRow
    exact Frame.mem_eventCuts.mpr (hPreserved.eventRows_subset (Frame.mem_eventCuts.mp hRow))

theorem Preparation.expandDiagram_high_eventCuts_eq
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    (Frame.ofMountain result).eventCuts.filter (fun row => decide (p.lastTop.row ≤ row)) =
      (Frame.ofMountain p.reduced).eventCuts.filter (fun row => decide (p.lastTop.row ≤ row)) := by
  apply ((Frame.ofMountain result).eventCuts_sorted.pairwise.filter _).eq_of_mem_iff
    ((Frame.ofMountain p.reduced).eventCuts_sorted.pairwise.filter _)
  intro row
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨(p.expandDiagram_high_eventCuts_iff hLast hCopies hRun h.2).mp h.1, h.2⟩
  · intro h
    exact ⟨(p.expandDiagram_high_eventCuts_iff hLast hCopies hRun h.2).mpr h.1, h.2⟩

noncomputable def Preparation.expandDiagram_high_event_sampling
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    Forests.EventSampling ((Frame.ofMountain p.reduced).highEventStart p.lastTop.row)
      (Frame.ofMountain p.reduced).lastEvent ((Frame.ofMountain result).highEventStart p.lastTop.row)
      (Frame.ofMountain result).lastEvent :=
  highEventTailSampling (Frame.ofMountain p.reduced) (Frame.ofMountain result) p.lastTop.row
    (p.expandDiagram_high_eventCuts_eq hLast hCopies hRun)

theorem Preparation.expandDiagram_high_event_sampling_rows
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {event : Nat} (hStart : (Frame.ofMountain result).highEventStart p.lastTop.row ≤ event)
    (hEnd : event ≤ (Frame.ofMountain result).lastEvent) :
    (Frame.ofMountain result).eventCut event =
      (Frame.ofMountain p.reduced).eventCut ((p.expandDiagram_high_event_sampling hLast hCopies hRun).sample event) :=
  highEventTailSampling_rows _ _ _ (p.expandDiagram_high_eventCuts_eq hLast hCopies hRun) hStart hEnd

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.pop_of_size
#print axioms OmegaY.Expansion.Preparation.expandDiagram_reduced_preserved
#print axioms OmegaY.Expansion.Preparation.expandDiagram_high_eventCuts_eq
#print axioms OmegaY.Expansion.Preparation.expandDiagram_high_event_sampling
#print axioms OmegaY.Expansion.Preparation.expandDiagram_high_event_sampling_rows
