/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNonmarkerLowRootRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNondirectBlocker
import OmegaY.Expansion.ActualLowRootCandidateRecognition

/-!
# Final recognition when the source candidate is below the bad root

The source candidate and its last blocker are selected by the actual
execution. The previously completed blocks lie strictly left of the final
current node, so their canonical recognition uses only the permitted
column induction hypothesis. No target path or numerical barrier is an
input to the final recognition theorem.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem low_root_candidate_recognition (hLast : 1 < last) {copies : Nat}
    (hCopies : 0 < copies) (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent candidate : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q execution.source = some candidate)
    (hCandidateRoot : candidate.1.val = p.root.column)
    (hCandidateBefore : candidate.2.val < p.root.index)
    (hRef : Frame.ref node = execution.copy.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  obtain ⟨comparison, hCurrentRef⟩ := execution.any_last_blocker hLast hParent hNondirect
  have hCurrent : comparison.pair.u = node := Executable.ref_injective _ (hCurrentRef.trans hRef.symm)
  have hCandidateEq : comparison.candidate = candidate :=
    Option.some.inj (comparison.source_candidate.symm.trans hCandidate)
  have hColumn : node.1.val = execution.source.1.val +
      origin.block * (p.reduced.size - 1 - p.root.column) :=
    (congrArg Ref.column hRef).trans execution.copy.source_column
  have hStartBefore : origin.start.size ≤ node.1.val := by
    have hSize := execution.copy.state.start_size
    have hSourceRight := execution.copy.state.next_lower
    omega
  have hP := comparison.recognize_low_root_candidate hLast (build_success_legal p.initial_build)
    hCopies hRun origin.start_run
    (by simpa only [hCandidateEq] using hCandidateRoot)
    ((congrArg (fun v => v.2.val) hCandidateEq).trans_lt hCandidateBefore)
    (fun current father hBefore hReal hRaw =>
      hLeft current father (hBefore.trans_le hStartBefore) hReal hRaw)
  have hRaw := comparison.pair.u_parent
  rw [hCurrent] at hRaw hP
  exact hRaw.trans hP.symm

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.low_root_candidate_recognition
