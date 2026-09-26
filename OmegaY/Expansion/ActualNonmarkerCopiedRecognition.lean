/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNonmarkerCopiedRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FinalActualBlockerValue
import OmegaY.Expansion.ActualNondirectBlocker

/-!
# Complete nondirect nonmarker recognition with a copied source parent

The source search selects its true final rejected record. Its actual
copied Q path and the complete transported depth word give the final
numerical barrier. The final current node is the original execution-origin
node. Only strict-left and strict-higher recognition are induction inputs.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

def SourceBlockerCopyPacket.toAnyRight
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
    (packet : SourceBlockerCopyPacket p block start references sourceU sourceParent result)
    (hParentRight : p.root.column < sourceParent.1.val) :
    AnySourceBlockerPacket p block start references sourceU sourceParent result :=
  { candidate := packet.candidate
    blocker := packet.blocker
    sourceUUpper := packet.sourceUUpper
    sourceZUpper := packet.sourceZUpper
    source_candidate := packet.source_candidate
    source_parent := packet.source_parent
    source_path := packet.source_path
    source_last_parent := packet.source_last_parent
    blocker_before := packet.blocker_before
    source_u_upper := packet.source_u_upper
    source_z_upper := packet.source_z_upper
    source_lower := packet.source_lower
    source_overlap := packet.source_overlap
    source_upper_height := packet.source_upper_height
    source_value := packet.source_value
    pair := packet.pair.toAny
      (hParentRight.trans (P_column_lt (build_normal_of_success p.reduced_build).toOrdered packet.source_last_parent))
      hParentRight }

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem nonmarker_right_recognition (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hParentRight : p.root.column < parent.1.val)
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
  have hBefore : execution.source.1.val < origin.sourceColumn + 1 := by
    rw [execution.source_column]
    omega
  rcases origin.after_state.recorded_nonmarker_last_blocker origin.after_history hLast
      hParent hParentRight hBefore (execution.unmarked_indices hUnmarked) with hDirect | hPacket
  · exact (hNondirect hDirect).elim
  · obtain ⟨packet⟩ := hPacket
    let comparison := packet.extend origin.preserved
    let anyPacket := packet.toAnyRight hParentRight
    have hCurrent : comparison.pair.u = node := Executable.ref_injective _
      (comparison.pair.u_ref.trans ((comparison.pair.uCopy.unique execution.copy).1.trans hRef.symm))
    have hAnyCurrent : (anyPacket.extend origin.preserved).pair.u = node := hCurrent
    have hLegal := build_success_legal p.initial_build
    have hBarrier := origin.after_state.preserved_blocker_barrier origin.after_history hLast origin.start_run
      anyPacket hBefore origin.preserved hLegal hRun
      (by simpa only [hAnyCurrent] using hLeft)
      (by simpa only [hAnyCurrent] using hHigher)
    have hP := comparison.recognize_of_nonmarker_barrier hLast
      (expandDiagram_valid_of_success hLegal hRun) (OmegaY.Expansion.expandDiagram_equations hLegal hRun).1
      (by simpa only [hCurrent] using hLeft) (execution.unmarked_indices hUnmarked) hParentRight hBarrier
    have hRaw := comparison.pair.u_parent
    rw [hCurrent] at hRaw hP
    exact hRaw.trans hP.symm

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.toAnyRight
#print axioms OmegaY.Expansion.ExecutedNodeCopy.nonmarker_right_recognition
