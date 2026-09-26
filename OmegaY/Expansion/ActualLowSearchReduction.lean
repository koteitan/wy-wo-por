/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowSearchReduction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FiniteRawSearchInduction
import OmegaY.Expansion.ActualHighNodeRecognition

/-!
# The remaining low copied-node recognition step

This file does not prove the low step. It states that outstanding local
obligation precisely and discharges all other numerical-search cases:
original columns, high copied nodes, and the finite induction itself.
Canonical reconstruction below remains conditional on that low step.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

/-- Outstanding local numerical recognition, only in new columns below Z.
The two premises refer strictly to earlier nodes in the finite induction.
This predicate is not assumed globally as an axiom and is not yet proved
for all actual expansions. -/
def Preparation.LowCopiedRecognitionStep {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain) : Prop :=
  ∀ (current father : (Frame.ofMountain result).Node),
    p.reduced.size ≤ current.1.val → Real current →
    (Frame.ofMountain result).height current < p.lastTop.row →
    (Frame.ofMountain result).rawParent current = some father →
    (∀ (node parent : (Frame.ofMountain result).Node),
      node.1.val < current.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent) →
    (∀ (node parent : (Frame.ofMountain result).Node), node.1 = current.1 →
      (Frame.ofMountain result).height current < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent) →
    (Frame.ofMountain result).P current = some father

/-- All node classes except the explicit low copied-node step are
discharged. No global left-column or higher-node premise remains. -/
theorem Preparation.rawParentSearch_of_low_copied_step
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hLow : p.LowCopiedRecognitionStep result) :
    (Frame.ofMountain result).RawParentSearch := by
  have hLegal := build_success_legal p.initial_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  apply rawParentSearch_of_strict_left_higher hValid.toOrdered
  intro current father hReal hRaw hLeft hHigher
  by_cases hOriginal : current.1.val < p.reduced.size
  · exact (p.expandDiagram_source_rawParent_eq_P hLast hCopies hRun hOriginal hReal).symm.trans hRaw
  · by_cases hHigh : p.lastTop.row ≤ (Frame.ofMountain result).height current
    · exact p.recognize_high_node hLast hCopies hRun hReal hHigh hRaw hLeft hHigher
    · exact hLow current father (by omega) hReal (lt_of_not_ge hHigh) hRaw hLeft hHigher

theorem Preparation.rawParent_eq_P_of_low_copied_step
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hLow : p.LowCopiedRecognitionStep result)
    {current : (Frame.ofMountain result).Node} (hReal : Real current) :
    (Frame.ofMountain result).rawParent current = (Frame.ofMountain result).P current := by
  have hLegal := build_success_legal p.initial_build
  exact (rawParentSearch_iff_agreement (expandDiagram_valid_of_success hLegal hRun)
    (OmegaY.Expansion.expandDiagram_equations hLegal hRun).1
    (OmegaY.Expansion.expandDiagram_equations hLegal hRun).2).mp
      (p.rawParentSearch_of_low_copied_step hLast hCopies hRun hLow) current hReal

theorem Preparation.normal_of_low_copied_step
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hLow : p.LowCopiedRecognitionStep result) : (Frame.ofMountain result).Normal := by
  have hLegal := build_success_legal p.initial_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  exact normal_of_raw_geometry_parent_search hValid
    (OmegaY.Expansion.expandDiagram_equations hLegal hRun).1
    (OmegaY.Expansion.expandDiagram_equations hLegal hRun).2
    (OmegaY.Expansion.expandDiagram_raw_geometry hLegal hRun)
    (mountainParentSearch_of_rawParentSearch hValid.toOrdered
      (p.rawParentSearch_of_low_copied_step hLast hCopies hRun hLow))

/-- Conditional exact reconstruction, including stored references, not
merely equality of the bottom numerical sequences. -/
theorem Preparation.reconstruct_of_low_copied_step
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hLow : p.LowCopiedRecognitionStep result)
    {values : List Nat} (hValues : valuesOf result = .ok values) :
    Canonical.build values = .ok result :=
  reconstruct_expansion_of_raw_parent_search (build_success_legal p.initial_build) hRun
    (p.rawParentSearch_of_low_copied_step hLast hCopies hRun hLow) hValues

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.rawParentSearch_of_low_copied_step
#print axioms OmegaY.Expansion.Preparation.rawParent_eq_P_of_low_copied_step
#print axioms OmegaY.Expansion.Preparation.normal_of_low_copied_step
#print axioms OmegaY.Expansion.Preparation.reconstruct_of_low_copied_step
