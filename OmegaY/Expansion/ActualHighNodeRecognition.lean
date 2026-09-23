/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighNodeRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighNodeOrigin

/-!
# High target rows in the actual numerical-search induction

This entrance accepts only the real final node and the strict-left /
strictly-higher induction hypotheses. Actual column coordinates recover
any copied source and its particular execution history, including earlier
blocks and the final truncation. Original complete columns are recognized
directly from their canonical source construction.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

/-- Full high-row agreement in a positive actual expansion. The caller
does not supply a source occurrence, source query, blocker, copying block,
intermediate history, or numerical comparison in the result. -/
theorem Preparation.high_node_rawParent_eq_P
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {current : (Frame.ofMountain result).Node} (hReal : Real current)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain result).height current)
    (hLeft : ∀ (node parent : (Frame.ofMountain result).Node),
      node.1.val < current.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent)
    (hHigher : ∀ (node parent : (Frame.ofMountain result).Node), node.1 = current.1 →
      (Frame.ofMountain result).height current < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent) :
    (Frame.ofMountain result).rawParent current = (Frame.ofMountain result).P current := by
  by_cases hOriginal : current.1.val < p.reduced.size
  · exact p.expandDiagram_source_rawParent_eq_P hLast hCopies hRun hOriginal hReal
  · obtain ⟨origin⟩ := p.high_copied_node_origin hLast hCopies hRun (by omega) hHigh
    exact origin.state.high_source_rawParent_eq_P origin.history origin.preserved hLast
      (build_success_legal p.initial_build) hCopies hRun origin.start_run origin.copy
      origin.source_before origin.source_high origin.target_ref hLeft hHigher

/-- The some-parent form used directly by raw-search induction. -/
theorem Preparation.recognize_high_node
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {current father : (Frame.ofMountain result).Node} (hReal : Real current)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain result).height current)
    (hRaw : (Frame.ofMountain result).rawParent current = some father)
    (hLeft : ∀ (node parent : (Frame.ofMountain result).Node),
      node.1.val < current.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent)
    (hHigher : ∀ (node parent : (Frame.ofMountain result).Node), node.1 = current.1 →
      (Frame.ofMountain result).height current < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent) :
    (Frame.ofMountain result).P current = some father :=
  (p.high_node_rawParent_eq_P hLast hCopies hRun hReal hHigh hLeft hHigher).symm.trans hRaw

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.high_node_rawParent_eq_P
#print axioms OmegaY.Expansion.Preparation.recognize_high_node
