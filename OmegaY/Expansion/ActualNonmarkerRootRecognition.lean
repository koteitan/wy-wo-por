/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNonmarkerRootRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootEffectiveCandidate
import OmegaY.Expansion.FinalActualBlockerValue
import OmegaY.Expansion.ActualNondirectBlocker

/-!
# Complete nondirect nonmarker recognition with a root-column source parent

The genuine source search forces its rejected candidate and final blocker
strictly right of the root. Their recorded effective copies yield the
actual new Q and its whole raw record path. The common boundary parent is
the exact endpoint already certified in the executed comparison packet.
The full transported word supplies the numerical barrier in the final
preserved output. Only strict-left and strict-higher recognition are inputs.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem nonmarker_root_recognition (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hParentRoot : parent.1.val = p.root.column)
    (hUnmarked : ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source))
    (hRef : Frame.ref node = execution.copy.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father)
    (hHigher : ∀ (current father : (Frame.ofMountain result).Node), current.1 = node.1 →
      (Frame.ofMountain result).height node < (Frame.ofMountain result).height current →
      Real current → (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hLegal := build_success_legal p.initial_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hSums := (OmegaY.Expansion.expandDiagram_equations hLegal hRun).1
  have hBefore : execution.source.1.val < origin.sourceColumn + 1 := by
    rw [execution.source_column]
    omega
  rcases origin.after_state.recorded_any_last_blocker origin.after_history hLast origin.start_run
      hParent execution.copy.state.next_lower hBefore with hDirect | hPacket
  · exact (hNondirect hDirect).elim
  · obtain ⟨packet⟩ := hPacket
    let comparison := packet.extend origin.preserved
    have hCurrent : comparison.pair.u = node := Executable.ref_injective _
      (comparison.pair.u_ref.trans ((comparison.pair.uCopy.unique execution.copy).1.trans hRef.symm))
    have hZRight : p.root.column < packet.blocker.1.val :=
      hParentRoot ▸ Frame.P_column_lt hNormal.toOrdered packet.source_last_parent
    have hQRight : p.root.column < packet.candidate.1.val :=
      hZRight.trans_le (packet.source_path.column_le hNormal.toOrdered)
    have hQBefore := (Frame.Q_column_lt hNormal.toOrdered packet.source_candidate).trans hBefore
    obtain ⟨candidateCopy⟩ := origin.after_state.prior_effective_occurrence origin.after_history
      hLast hQRight hQBefore
    obtain ⟨zCopy, hZRefLocal, _⟩ :
        ∃ zCopy : EffectiveCopyOccurrence p origin.block origin.start origin.references
            packet.blocker (origin.before.push origin.column),
          Frame.ref packet.pair.z = zCopy.outputRef ∧
          (Frame.ofMountain (origin.before.push origin.column)).cell packet.pair.z = zCopy.read.outputCell := by
      rcases packet.pair.z_origin with ⟨hFixed, _⟩ | ⟨_, zCopy, hRef, hCell⟩
      · exact (not_lt_of_ge hFixed hZRight).elim
      · exact ⟨zCopy, hRef, hCell⟩
    have hZRef : Frame.ref comparison.pair.z = (zCopy.extend origin.preserved).outputRef := by
      change Frame.ref (origin.preserved.mapNode packet.pair.z) = zCopy.outputRef
      rw [origin.preserved.mapNode_ref]
      exact hZRefLocal
    have copiedPath := (origin.after_state.recorded_effective_path origin.after_history hLast
      packet.source_path hZRight hQBefore candidateCopy zCopy).preserve origin.preserved
    have hDistinct : packet.candidate ≠ parent := by
      intro he
      exact hNondirect (he ▸ packet.source_candidate)
    obtain ⟨actual, candidate, hActualRef, hCandidateRef, hQ, _⟩ :=
      comparison.pair.uCopy.candidate_eq_nondirect_nonmarker_of_parent_ge hLast hValid
        (execution.unmarked_indices hUnmarked) (candidateCopy.extend origin.preserved)
        packet.source_parent packet.source_candidate hParentRoot.ge hDistinct
    have hActual : actual = comparison.pair.u := Executable.ref_injective _
      (hActualRef.trans comparison.pair.u_ref.symm)
    subst actual
    have hLeftAtU : ∀ (current father : G.Node), current.1.val < comparison.pair.u.1.val →
        Real current → G.rawParent current = some father → G.P current = some father := by
      simpa only [hCurrent] using hLeft
    have hHigherAtU : ∀ (current father : G.Node), current.1 = comparison.pair.u.1 →
        G.height comparison.pair.u < G.height current → Real current →
        G.rawParent current = some father → G.P current = some father := by
      simpa only [hCurrent] using hHigher
    have path := copiedPath.toParentPath_of_recognition hValid.toOrdered hLeftAtU
      hCandidateRef hZRef (Frame.Q_real hValid.toOrdered comparison.pair.u_real hQ)
      (Frame.Q_column_lt hValid.toOrdered hQ)
    have hZP := hLeftAtU comparison.pair.z comparison.pair.parent
      ((path.column_le hValid.toOrdered).trans_lt (Frame.Q_column_lt hValid.toOrdered hQ))
      comparison.pair.z_real comparison.pair.z_parent
    obtain ⟨actualParent, hActualParent, _, _, hSmall, _⟩ :=
      hSums.rawParent_upper hValid comparison.pair.u_real comparison.pair.u_upper
    have he : actualParent = comparison.pair.parent :=
      Option.some.inj (hActualParent.symm.trans comparison.pair.u_parent)
    subst actualParent
    have hBarrier := origin.after_state.preserved_blocker_barrier origin.after_history hLast
      origin.start_run packet hBefore origin.preserved hLegal hRun hLeftAtU
      hHigherAtU
    have hP := Frame.P_of_record_barrier hValid.toOrdered hQ path hZP hBarrier hSmall
    have hRaw := comparison.pair.u_parent
    rw [hCurrent] at hRaw hP
    exact hRaw.trans hP.symm

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.nonmarker_root_recognition
