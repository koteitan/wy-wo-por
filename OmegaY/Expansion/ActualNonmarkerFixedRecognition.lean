/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNonmarkerFixedRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNondirectBlocker
import OmegaY.Expansion.ActualFixedCandidateRecognition

/-!
# Origin-derived final recognition for a fixed source candidate

The true source search and final copied current are recovered from the
execution packet. A source candidate in the good part has its whole record
path preserved, and the numerical barrier is an exact unchanged-value
comparison. No induction hypothesis on numerical recognition is needed.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem fixed_candidate_recognition (hLast : 1 < last) {copies : Nat}
    (hCopies : 0 < copies) (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent candidate : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q execution.source = some candidate)
    (hCandidateFixed : candidate.1.val < p.root.column)
    (hRef : Frame.ref node = execution.copy.outputRef) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  obtain ⟨comparison, hCurrentRef⟩ := execution.any_last_blocker hLast hParent hNondirect
  have hCurrent : comparison.pair.u = node := Executable.ref_injective _ (hCurrentRef.trans hRef.symm)
  have hCandidateEq : comparison.candidate = candidate :=
    Option.some.inj (comparison.source_candidate.symm.trans hCandidate)
  have hP := comparison.recognize_fixed_candidate hLast (build_success_legal p.initial_build)
    hCopies hRun (by simpa only [hCandidateEq] using hCandidateFixed)
  have hRaw := comparison.pair.u_parent
  rw [hCurrent] at hRaw hP
  exact hRaw.trans hP.symm

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.fixed_candidate_recognition
