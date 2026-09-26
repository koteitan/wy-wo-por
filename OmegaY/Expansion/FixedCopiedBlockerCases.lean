/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FixedCopiedBlockerCases.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCopiedFixedBlockerRecognition

/-!
# The remaining fixed-parent search must cross the boundary

The successful source search supplies its actual final rejected record.
If that record is in the copied part, actual candidate and path recognition
are complete. Consequently, the only remaining branch has a genuine source
blocker in or to the left of the root column. The returned packet contains
the actual local execution and source path, not a target search hypothesis.
-/

namespace OmegaY.Expansion
open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem fixed_nondirect_blocker_cases (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hFixed : parent.1.val < p.root.column)
    (hRef : Frame.ref node = execution.copy.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node ∨
      ∃ packet : AnySourceBlockerPacket p origin.block origin.start origin.references execution.source parent
          (origin.before.push origin.column), packet.blocker.1.val ≤ p.root.column := by
  have hBefore : execution.source.1.val < origin.sourceColumn + 1 := by
    rw [execution.source_column]
    omega
  rcases origin.after_state.recorded_any_last_blocker origin.after_history hLast origin.start_run
      hParent execution.copy.state.next_lower hBefore with hDirect | hPacket
  · exact (hNondirect hDirect).elim
  · obtain ⟨packet⟩ := hPacket
    by_cases hRight : p.root.column < packet.blocker.1.val
    · exact Or.inl (execution.fixed_copied_blocker_recognition
        hLast hRun packet hFixed hRight hRef hLeft)
    · exact Or.inr ⟨packet, le_of_not_gt hRight⟩

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.fixed_nondirect_blocker_cases
