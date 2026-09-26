/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinalActualBlockerValue.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCopiedBlockerWord
import OmegaY.Expansion.PreservedCopiedBarrier
import OmegaY.Expansion.ActualFixedBlockerValue

/-!
# Actual blocker values in every preserved final output

For a copied blocker, actual complete depth-word transport supplies the
numerical barrier. For an unchanged blocker, the common source parent is
in the good part and actual values are unchanged. Both branches retain
the true column execution and final preservation. No target value or word
comparison is assumed. Recognition is used only strictly left or higher.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block previousCopies next : Nat} {start ambient result : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range previousCopies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent ambient)
  (hBefore : sourceU.1.val < next) (preserved : PreservesColumns ambient result)
  {input : List Nat} (hLegal : Canonical.Legal input) {copies : Nat}
  (hRun : expandDiagram input copies = .ok result)
  (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
    node.1.val < (packet.extend preserved).pair.u.1.val → Real node →
    (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
  (hHigher : ∀ (node father : (Frame.ofMountain result).Node),
    node.1 = (packet.extend preserved).pair.u.1 →
    (Frame.ofMountain result).height (packet.extend preserved).pair.u < (Frame.ofMountain result).height node →
    Real node → (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)

include s history hLast hStartRun hBefore hLegal hRun hLeft hHigher

theorem DynamicBlockState.preserved_copied_blocker_barrier
    (hBlockerRight : p.root.column < packet.blocker.1.val) :
    (Frame.ofMountain result).value (packet.extend preserved).pair.u ≤
      (Frame.ofMountain result).value (packet.extend preserved).pair.z := by
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hWidth : 0 < ambient.size := (Nat.zero_le packet.pair.u.1.val).trans_lt packet.pair.u.1.isLt
  have hUColumn : packet.pair.u.1.val = sourceU.1.val + block * (p.reduced.size - 1 - p.root.column) :=
    (congrArg Ref.column packet.pair.u_ref).trans packet.pair.uCopy.source_column
  have hPrefix : start.size ≤ (packet.extend preserved).pair.u.1.val := by
    change start.size ≤ (preserved.mapNode packet.pair.u).1.val
    rw [preserved.mapNode_column, hUColumn, s.start_size]
    have hRight := packet.pair.uCopy.state.next_lower
    omega
  have hKnown : ∀ (node father : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some father →
        (Frame.ofMountain ambient).P node = some father := by
    intro node father hColumn hReal hRaw
    have hMapped := hLeft (preserved.mapNode node) (preserved.mapNode father)
      (by rw [preserved.mapNode_column]; exact hColumn.trans_le hPrefix)
      (preserved.mapNode_real hReal) (preserved.mapNode_rawParent hRaw)
    apply (Executable.findParent_ref_iff s.ambient_valid.toOrdered node father).mp
    rw [← preserved.findParent node.1.isLt]
    simpa only [preserved.mapNode_ref] using
      (Executable.findParent_ref_iff hValid.toOrdered _ _).mpr hMapped
  have hWord := s.actual_copied_blocker_word history hLast hStartRun packet hBefore hBlockerRight hKnown
  exact packet.preserved_barrier_of_word preserved s.ambient_valid.toOrdered hWidth
    hLegal hRun hLeft hHigher hWord

theorem DynamicBlockState.preserved_blocker_barrier :
    (Frame.ofMountain result).value (packet.extend preserved).pair.u ≤
      (Frame.ofMountain result).value (packet.extend preserved).pair.z := by
  by_cases hBlockerRight : p.root.column < packet.blocker.1.val
  · exact s.preserved_copied_blocker_barrier history hLast hStartRun packet hBefore preserved
      hLegal hRun hLeft hHigher hBlockerRight
  · exact (packet.extend preserved).unchanged_blocker_barrier hLast hLegal hRun (le_of_not_gt hBlockerRight)

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.preserved_copied_blocker_barrier
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_blocker_barrier
