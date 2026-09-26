/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedCopiedBarrier.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PreservedDepthWords
import OmegaY.Expansion.PreservedAnyLastBlocker
import OmegaY.Expansion.DepthWordStart
import OmegaY.Expansion.HighEventSuffix

/-!
# From an executed prefix word to the final numerical blocker barrier

Later complete columns and the final truncation preserve the retained
comparison nodes. The actual final event enumeration is sampled anew at
the retained common upper row. Full-width words are then converted to the
current-column bound of the numerical comparison theorem. Recognition is
used only strictly left of, or strictly higher than, the current node.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start ambient result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent ambient)
  (preserved : PreservesColumns ambient result)

theorem preserved_barrier_of_word
    (hAmbient : (Frame.ofMountain ambient).Ordered)
    (hSourceWidth : 0 < ambient.size)
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
    (hWord : Forests.DepthWordLe
      ((Frame.ofMountain ambient).frontierForests (bottomCandidateMap (ambient.size - 1))
        (eventFrontierNat hAmbient hSourceWidth) (ambient.size - 1))
      ((Frame.ofMountain ambient).highEventStart ((Frame.ofMountain ambient).height packet.pair.uUpper))
      (Frame.ofMountain ambient).lastEvent packet.pair.u.1.val packet.pair.z.1.val) :
    (Frame.ofMountain result).value (packet.extend preserved).pair.u ≤
      (Frame.ofMountain result).value (packet.extend preserved).pair.z := by
  let comparison := packet.extend preserved
  let T := Frame.ofMountain result
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hWidth : 0 < result.size := (Nat.zero_le comparison.pair.u.1.val).trans_lt comparison.pair.u.1.isLt
  have hUpperReal : Real packet.pair.uUpper := upper_real packet.pair.u_upper
  have hThreshold := real_height_mem_eventCuts hAmbient hUpperReal
  have hTransport := (preserved.depth_words_at_retained_row hAmbient hValid.toOrdered
    hSourceWidth hWidth hThreshold packet.pair.u.1.isLt packet.pair.z.1.isLt).2.2.mpr hWord
  have hUColumn : comparison.pair.u.1.val = packet.pair.u.1.val := preserved.mapNode_column packet.pair.u
  have hZColumn : comparison.pair.z.1.val = packet.pair.z.1.val := preserved.mapNode_column packet.pair.z
  have hUpperRow : T.height comparison.pair.uUpper = (Frame.ofMountain ambient).height packet.pair.uUpper :=
    preserved.mapNode_height packet.pair.uUpper
  obtain ⟨event, hEnd, hCut, hComparison⟩ := comparison.target_depth_word_comparison hLegal hRun hLeft hHigher
  have hStart : T.highEventStart ((Frame.ofMountain ambient).height packet.pair.uUpper) = event + 1 := by
    rw [← hUpperRow, ← hCut]
    exact T.highEventStart_eventCut (Nat.succ_le_of_lt hEnd)
  rw [hStart, ← hUColumn, ← hZColumn] at hTransport
  have hBounds := Frame.depthWord_bound_iff hValid.toOrdered hWidth
    (bottomCandidateMap comparison.pair.u.1.val) (bottomCandidateMap (result.size - 1))
    (start := event + 1) (finish := T.lastEvent) comparison.pair.u.1.isLt le_rfl comparison.pair.z_column
  exact hComparison.mp (hBounds.2.2.mpr hTransport)

end AnySourceBlockerPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.AnySourceBlockerPacket.preserved_barrier_of_word
