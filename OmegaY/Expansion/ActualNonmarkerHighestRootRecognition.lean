/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNonmarkerHighestRootRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNondirectBlocker
import OmegaY.Expansion.ActualHighestRootCandidateRecognition

/-!
# Final low-node recognition at the highest source root candidate

The highest-boundary projection and its numerical barrier are derived
from the genuine execution. Only the strict-left induction hypothesis is
used to recognize the completed block prefix.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem highest_root_candidate_recognition_low (hLast : 1 < last) {copies : Nat}
    (hCopies : 0 < copies) (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent candidate : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q execution.source = some candidate)
    (hCandidateRoot : Frame.ref candidate = p.root)
    (hLow : (Frame.ofMountain result).height node < p.lastTop.row)
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
  have hCell := Canonical.cellAt_of_frame_node result node
  rw [hRef, execution.copy.output_read] at hCell
  have hRow : (Frame.ofMountain result).height node = execution.copy.read.outputCell.row :=
    congrArg Cell.row ((Except.ok.inj hCell).symm)
  have hSourceLow := execution.copy.read.source_row_le_output.trans_lt (hRow ▸ hLow)
  have hP := comparison.recognize_highest_root_candidate_low hLast
    (build_success_legal p.initial_build) hCopies hRun origin.start_run
    ((congrArg Frame.ref hCandidateEq).trans hCandidateRoot) hSourceLow
    (fun current father hBefore hReal hRaw =>
      hLeft current father (hBefore.trans_le hStartBefore) hReal hRaw)
  have hRaw := comparison.pair.u_parent
  rw [hCurrent] at hRaw hP
  exact hRaw.trans hP.symm

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.highest_root_candidate_recognition_low
