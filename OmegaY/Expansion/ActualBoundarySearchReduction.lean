/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualBoundarySearchReduction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNonmarkerCopiedRecognition
import OmegaY.Expansion.ActualNonmarkerFixedRecognition
import OmegaY.Expansion.FinalPhysicalMarkerRecognition

/-!
# The remaining search crosses the root boundary from a nonmarker

All actual gaps, physical markers, direct hits, nonmarkers with a copied
source parent, and fixed-candidate searches are discharged. The sole
remaining predicate retains a genuine nonmarker execution whose accepted
source parent is at or left of the root and whose initial candidate is at
or right of the root. The handler for that predicate is still outstanding.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

def BoundaryNonmarkerAt {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (node : (Frame.ofMountain result).Node) : Prop :=
  ∃ (origin : CopiedNodeOrigin p result node) (execution : ExecutedNodeCopy origin)
    (parent candidate : (Frame.ofMountain p.reduced).Node),
    (Frame.ofMountain p.reduced).P execution.source = some parent ∧
    (Frame.ofMountain p.reduced).Q execution.source = some candidate ∧
    candidate ≠ parent ∧ parent.1.val ≤ p.root.column ∧ p.root.column ≤ candidate.1.val ∧
    ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source) ∧
    Frame.ref node = execution.copy.outputRef

theorem Preparation.low_copied_step_of_boundary_nonmarker
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hBoundary : p.LowRecognitionOn result (BoundaryNonmarkerAt p result)) :
    p.LowCopiedRecognitionStep result := by
  apply p.low_copied_step_of_nondirect_nonmarker hLast hCopies hRun
  rintro current father hColumn hReal hLow ⟨origin, execution, parent, hParent, hNondirect, hUnmarked, hRef⟩ hRaw hLeft hHigher
  by_cases hParentRight : p.root.column < parent.1.val
  · exact (execution.nonmarker_right_recognition hLast hRun hParent hNondirect
      hParentRight hUnmarked hRef hLeft hHigher).symm.trans hRaw
  · obtain ⟨candidate, hCandidate, _⟩ := (P_iff (build_normal_of_success p.reduced_build).toOrdered).mp hParent
    by_cases hFixed : candidate.1.val < p.root.column
    · exact (execution.fixed_candidate_recognition hLast hCopies hRun hParent hNondirect
        hCandidate hFixed hRef).symm.trans hRaw
    · apply hBoundary current father hColumn hReal hLow _ hRaw hLeft hHigher
      refine ⟨origin, execution, parent, candidate, hParent, hCandidate, ?_,
        le_of_not_gt hParentRight, le_of_not_gt hFixed, hUnmarked, hRef⟩
      intro he
      exact hNondirect (he ▸ hCandidate)

theorem Preparation.rawParentSearch_of_boundary_nonmarker
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hBoundary : p.LowRecognitionOn result (BoundaryNonmarkerAt p result)) :
    (Frame.ofMountain result).RawParentSearch :=
  p.rawParentSearch_of_low_copied_step hLast hCopies hRun
    (p.low_copied_step_of_boundary_nonmarker hLast hCopies hRun hBoundary)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.low_copied_step_of_boundary_nonmarker
#print axioms OmegaY.Expansion.Preparation.rawParentSearch_of_boundary_nonmarker
