/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCanonicalReconstruction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootCrossingRecognition

/-!
# Canonical reconstruction of every actual finite-copy expansion

The finite column/reverse-index induction now has its complete local step.
Thus every stored real parent equals the numerical first-smaller ancestor
parent. Actual backfill equations, tops, bottom legs and row geometry then
reconstruct the exact returned graph, including every row and reference.
No copied normality, comparison oracle, row bound, or expansion termination
assumption is a premise. Well-foundedness of repeated expansion is separate.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem expandDiagram_rawParentSearch {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result) :
    (Frame.ofMountain result).RawParentSearch := by
  by_cases hTrivial : values.isEmpty ∨ values.getLast? = some 1 ∨ copies = 0
  · exact expandDiagram_trivial_rawParentSearch hLegal hRun hTrivial
  · rcases hLegal with rfl | ⟨rest, rfl, hPositive⟩
    · simp at hTrivial
    · rcases List.eq_nil_or_concat' rest with rfl | ⟨middle, last, rfl⟩
      · simp at hTrivial
      · have hLastPositive : 0 < last := hPositive last (by simp)
        have hLastNe : last ≠ 1 := by
          intro hLast
          apply hTrivial
          right; left
          change ((1 :: middle) ++ [last]).getLast? = some 1
          rw [List.getLast?_append]
          simp [hLast]
        have hLast : 1 < last := by omega
        have hCopies : 0 < copies := by
          by_contra h
          apply hTrivial
          right; right
          omega
        obtain ⟨p⟩ := preparation_total middle last
          (fun value hv => hPositive value (by simp [hv])) hLast
        exact p.rawParentSearch_of_low_copied_step hLast hCopies hRun
          (p.low_copied_recognition_step hLast hCopies hRun)

theorem expandDiagram_normal {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result) :
    (Frame.ofMountain result).Normal := by
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hEquations := expandDiagram_equations hLegal hRun
  exact normal_of_raw_geometry_parent_search hValid hEquations.1 hEquations.2
    (expandDiagram_raw_geometry hLegal hRun)
    (mountainParentSearch_of_rawParentSearch hValid.toOrdered (expandDiagram_rawParentSearch hLegal hRun))

theorem expandDiagram_rawParent_eq_P {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result)
    {node : (Frame.ofMountain result).Node} (hReal : Real node) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node :=
  (expandDiagram_normal hLegal hRun).rawParent_eq_P hReal

theorem expandDiagram_reconstruct {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram values copies = .ok mountain)
    {output : List Nat} (hValues : valuesOf mountain = .ok output) :
    Canonical.build output = .ok mountain :=
  reconstruct_expansion_of_raw_parent_search hLegal hRun
    (expandDiagram_rawParentSearch hLegal hRun) hValues

theorem expandDiagram_reconstruct_bottom {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram values copies = .ok mountain) :
    Canonical.build (bottomValues mountain) = .ok mountain :=
  expandDiagram_reconstruct hLegal hRun
    (valuesOf_eq_bottomValues (expandDiagram_valid_of_success hLegal hRun))

/-- Every finite-copy run succeeds, returns a legal sequence, and its actual
stored output mountain is precisely the canonical build of that sequence.
The quantification is over all syntactically legal inputs, not just seeds.
-/
theorem expand_total_canonical {values : List Nat} (hLegal : Legal values) (copies : Nat) :
    ∃ output mountain,
      expandDiagram values copies = .ok mountain ∧ expand values copies = .ok output ∧
      Legal output ∧ Canonical.build output = .ok mountain ∧ (Frame.ofMountain mountain).Normal := by
  obtain ⟨mountain, hDiagram, hValid⟩ := expandDiagram_total hLegal copies
  obtain ⟨output, hValues, hOutputLegal, _⟩ := valuesOf_total_legal hValid
  refine ⟨output, mountain, hDiagram, ?_, hOutputLegal,
    expandDiagram_reconstruct hLegal hDiagram hValues, expandDiagram_normal hLegal hDiagram⟩
  unfold expand
  rw [hDiagram]
  exact hValues

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_rawParentSearch
#print axioms OmegaY.Expansion.expandDiagram_normal
#print axioms OmegaY.Expansion.expandDiagram_rawParent_eq_P
#print axioms OmegaY.Expansion.expandDiagram_reconstruct
#print axioms OmegaY.Expansion.expandDiagram_reconstruct_bottom
#print axioms OmegaY.Expansion.expand_total_canonical
