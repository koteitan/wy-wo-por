/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootCrossingRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualGoodBoundaryReduction
import OmegaY.Expansion.CandidateBoundaryProjection
import OmegaY.Expansion.RootBoundaryTailRecognition

/-!
# Complete low copied-node numerical recognition

The true source search either is already recognized or supplies its actual
root crossing. Candidate-to-boundary projection and the boundary-tail
barrier then recognize the original final node. Both bridges use only the
strictly earlier completed columns. No candidate path, comparison, copied
normality, or residual recognition handler is an input to the low-step theorem.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem fixed_root_crossing_recognition_low (hLast : 1 < last) {copies : Nat}
    (hCopies : 0 < copies) (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent root : (Frame.ofMountain p.reduced).Node}
    (packet : AnySourceBlockerPacket p origin.block origin.start origin.references
      execution.source parent (origin.before.push origin.column))
    (hFixed : parent.1.val < p.root.column)
    (hCandidateRight : p.root.column < packet.candidate.1.val)
    (hRootReal : Real root) (hRootColumn : root.1.val = p.root.column)
    (rootPath : ParentPath (Frame.ofMountain p.reduced) packet.candidate root)
    (tail : ParentPath (Frame.ofMountain p.reduced) root packet.blocker)
    (hRootLow : (Frame.ofMountain p.reduced).height root ≤ execution.copy.read.outputCell.row)
    (hRootHigh : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      execution.copy.read.outputCell.row < (Frame.ofMountain p.reduced).height upper)
    (hLow : (Frame.ofMountain result).height node < p.lastTop.row)
    (hRef : Frame.ref node = execution.copy.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  let comparison := packet.extend origin.preserved
  let preserved := origin.state.start_preserved.trans
    ((PreservesColumns.push origin.before origin.column).trans origin.preserved)
  have hCurrent : comparison.pair.u = node := Executable.ref_injective _
    (comparison.pair.u_ref.trans ((comparison.pair.uCopy.unique execution.copy).1.trans hRef.symm))
  obtain ⟨q, boundary, hCut, hQ, hBoundaryColumn, hBoundaryFront, path⟩ :=
    execution.candidate_root_boundary_path hLast hRun packet.source_parent hFixed
      packet.source_candidate hCandidateRight rootPath hRootColumn hRef hLeft
  have hRead := Canonical.cellAt_of_frame_node result node
  rw [hRef, execution.copy.output_read] at hRead
  have hRow : (Frame.ofMountain result).height node = execution.copy.read.outputCell.row :=
    congrArg Cell.row (Except.ok.inj hRead).symm
  have hStartBefore : origin.start.size ≤ node.1.val :=
    origin.state.start_preserved.size_le.trans_eq origin.target_column
  have hWidth : 0 < origin.start.size := by
    have hSize := origin.state.start_size
    omega
  have hP := comparison.recognize_of_root_boundary_path hLast hCopies hRun origin.start_run
    preserved origin.state.start_valid hWidth hRootReal hRootColumn tail
    (by simpa only [hCurrent, hRow] using hRootLow)
    (by simpa only [hCurrent, hRow] using hRootHigh)
    (by simpa only [hCurrent] using hLow)
    (fun current father hBefore hReal hRaw =>
      hLeft current father (hBefore.trans_le hStartBefore) hReal hRaw)
    (by simpa only [hCurrent] using hQ) hBoundaryColumn
    (by simpa only [hCurrent] using hBoundaryFront) path
  have hRaw := comparison.pair.u_parent
  rw [hCurrent] at hRaw hP
  exact hRaw.trans hP.symm

end ExecutedNodeCopy

/-- Unconditional remaining finite-induction step for the real expansion.
The strict-left/strict-higher premises are bound by `LowCopiedRecognitionStep`
and are discharged by its already proved finite column/index induction.
-/
theorem Preparation.low_copied_recognition_step
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    p.LowCopiedRecognitionStep result := by
  apply p.low_copied_step_of_good_boundary_packet hLast hCopies hRun
  rintro current father _ _ hLow ⟨origin, execution, parent, oldPacket,
    hFixed, _, hCandidateRight, _, hRef⟩ hRaw hLeft _
  have hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent := by
    intro he
    have hEq := Option.some.inj (oldPacket.source_candidate.symm.trans he)
    have hColumn := congrArg (fun v => v.1.val) hEq
    omega
  rcases execution.fixed_copied_candidate_root_cases hLast hRun oldPacket.source_parent
      hNondirect hFixed oldPacket.source_candidate hCandidateRight hRef hLeft with
      hRecognized | ⟨packet, root, hRootColumn, hRootReal, _, rootPath, tail, hRootLow, hRootHigh⟩
  · exact hRecognized.symm.trans hRaw
  · have hCandidateEq : packet.candidate = oldPacket.candidate :=
      Option.some.inj (packet.source_candidate.symm.trans oldPacket.source_candidate)
    have hRight : p.root.column < packet.candidate.1.val := by
      simpa only [hCandidateEq] using hCandidateRight
    exact (execution.fixed_root_crossing_recognition_low hLast hCopies hRun packet hFixed hRight
      hRootReal hRootColumn rootPath tail hRootLow hRootHigh hLow hRef hLeft).symm.trans hRaw

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.fixed_root_crossing_recognition_low
#print axioms OmegaY.Expansion.Preparation.low_copied_recognition_step
