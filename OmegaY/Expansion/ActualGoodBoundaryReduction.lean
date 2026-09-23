/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualGoodBoundaryReduction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualBoundarySearchReduction
import OmegaY.Expansion.ActualNonmarkerRootRecognition
import OmegaY.Expansion.ActualNonmarkerLowRootRecognition
import OmegaY.Expansion.ActualNonmarkerHighestRootRecognition
import OmegaY.Expansion.FixedCopiedBlockerCases

/-!
# Only genuine fixed-parent boundary-crossing packets remain

All root-parent searches and all low root-candidate searches are proved.
A root-column candidate strictly above the bad root cannot occur at a low
output node. A copied last blocker is also discharged. The still-unproved
handler therefore concerns a true fixed-parent execution with an unchanged
blocker and a candidate strictly right of the root. It is an explicit
remaining obligation, not an assertion of canonical reconstruction.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

def GoodBoundaryPacketAt {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (node : (Frame.ofMountain result).Node) : Prop :=
  ∃ (origin : CopiedNodeOrigin p result node) (execution : ExecutedNodeCopy origin)
    (parent : (Frame.ofMountain p.reduced).Node)
    (packet : AnySourceBlockerPacket p origin.block origin.start origin.references
      execution.source parent (origin.before.push origin.column)),
    parent.1.val < p.root.column ∧ packet.blocker.1.val ≤ p.root.column ∧
    p.root.column < packet.candidate.1.val ∧
    ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source) ∧
    Frame.ref node = execution.copy.outputRef

theorem Preparation.low_copied_step_of_good_boundary_packet
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hBoundary : p.LowRecognitionOn result (GoodBoundaryPacketAt p result)) :
    p.LowCopiedRecognitionStep result := by
  apply p.low_copied_step_of_boundary_nonmarker hLast hCopies hRun
  rintro current father hColumn hReal hLow
    ⟨origin, execution, parent, candidate, hParent, hCandidate, hDistinct,
      hParentLe, hCandidateGe, hUnmarked, hRef⟩ hRaw hLeft hHigher
  have hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent := by
    intro he
    exact hDistinct (Option.some.inj (hCandidate.symm.trans he))
  by_cases hParentRoot : parent.1.val = p.root.column
  · exact (execution.nonmarker_root_recognition hLast hRun hParent hNondirect
      hParentRoot hUnmarked hRef hLeft hHigher).symm.trans hRaw
  have hParentGood : parent.1.val < p.root.column := lt_of_le_of_ne hParentLe hParentRoot
  by_cases hRoot : candidate.1.val = p.root.column
  · by_cases hBefore : candidate.2.val < p.root.index
    · exact (execution.low_root_candidate_recognition hLast hCopies hRun
        hParent hNondirect hCandidate hRoot hBefore hRef hLeft).symm.trans hRaw
    · by_cases hAt : candidate.2.val = p.root.index
      · exact (execution.highest_root_candidate_recognition_low hLast hCopies hRun
          hParent hNondirect hCandidate (congrArg₂ Ref.mk hRoot hAt) hLow hRef hLeft).symm.trans hRaw
      · have hHigh := p.root_node_after_badRoot_is_high hLast hRoot (by omega)
        have hRange := (Frame.Q_height_le (build_normal_of_success p.reduced_build).toOrdered
          hCandidate).trans execution.copy.read.source_row_le_output
        have hCell := Canonical.cellAt_of_frame_node result current
        rw [hRef, execution.copy.output_read] at hCell
        have hRow : (Frame.ofMountain result).height current = execution.copy.read.outputCell.row :=
          congrArg Cell.row ((Except.ok.inj hCell).symm)
        exact False.elim (not_lt_of_ge ((hHigh.trans hRange).trans_eq hRow.symm) hLow)
  have hCandidateRight : p.root.column < candidate.1.val := lt_of_le_of_ne hCandidateGe (Ne.symm hRoot)
  rcases execution.fixed_nondirect_blocker_cases hLast hRun hParent hNondirect
      hParentGood hRef hLeft with hRecognized | ⟨packet, hBlocker⟩
  · exact hRecognized.symm.trans hRaw
  · have hCandidateEq : packet.candidate = candidate :=
      Option.some.inj (packet.source_candidate.symm.trans hCandidate)
    apply hBoundary current father hColumn hReal hLow _ hRaw hLeft hHigher
    exact ⟨origin, execution, parent, packet, hParentGood, hBlocker,
      (congrArg (fun v => v.1.val) hCandidateEq).symm ▸ hCandidateRight, hUnmarked, hRef⟩

theorem Preparation.rawParentSearch_of_good_boundary_packet
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hBoundary : p.LowRecognitionOn result (GoodBoundaryPacketAt p result)) :
    (Frame.ofMountain result).RawParentSearch :=
  p.rawParentSearch_of_low_copied_step hLast hCopies hRun
    (p.low_copied_step_of_good_boundary_packet hLast hCopies hRun hBoundary)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.low_copied_step_of_good_boundary_packet
#print axioms OmegaY.Expansion.Preparation.rawParentSearch_of_good_boundary_packet
