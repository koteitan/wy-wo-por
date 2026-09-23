/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualBlockerDepthWords.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLastBlockerPair

/-!
# The two actual depth-word obligations of a copied source blocker

The source search gives the source word inequality at its genuine upper
event. The copied packet determines its genuine comparison event and
reduces the desired copied numerical barrier to a target word inequality.
The missing bridge is precisely transport between these actual words;
this module does not replace it by the source inequality itself.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

namespace SourceBlockerCopyPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : SourceBlockerCopyPacket p block start references sourceU sourceParent result)

theorem source_depth_word :
    let F := Frame.ofMountain p.reduced
    let hN := build_normal_of_success p.reduced_build
    let hWidth := (Nat.zero_le sourceU.1.val).trans_lt sourceU.1.isLt
    let forests := F.frontierForests (bottomCandidateMap sourceU.1.val)
      (eventFrontierNat hN.toOrdered hWidth) sourceU.1.val
    ∃ event, event < F.lastEvent ∧ F.eventCut (event + 1) = F.height packet.sourceUUpper ∧
      Forests.DepthWordLe forests (event + 1) F.lastEvent sourceU.1.val packet.blocker.1.val := by
  let F := Frame.ofMountain p.reduced
  have hWidth : 0 < p.reduced.size := (Nat.zero_le sourceU.1.val).trans_lt sourceU.1.isLt
  obtain ⟨uUpper, event, hUpper, hEvent, _, hCut, _, _, _, _, hCompare⟩ :=
    build_common_parent_upper_depthWord p.reduced_build hWidth sourceU.1.isLt le_rfl packet.blocker_before.le
      packet.source_parent packet.source_last_parent packet.source_z_upper packet.source_lower packet.source_overlap
  have he : uUpper = packet.sourceUUpper := Option.some.inj (hUpper.symm.trans packet.source_u_upper)
  exact ⟨event, hEvent, he ▸ hCut, hCompare.mpr packet.source_value⟩

/-- In an actual expansion, the target packet supplies all common-parent
and common-upper data required for numerical comparison. The current raw
parent is still not assumed recognized. -/
theorem target_depth_word_comparison
    {input : List Nat} (hLegal : Canonical.Legal input) {copies : Nat}
    (hRun : expandDiagram input copies = .ok result)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (hHigh : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father) :
    let F := Frame.ofMountain result
    let hValid := expandDiagram_valid_of_success hLegal hRun
    let hWidth := (Nat.zero_le packet.pair.u.1.val).trans_lt packet.pair.u.1.isLt
    let forests := F.frontierForests (bottomCandidateMap packet.pair.u.1.val)
      (eventFrontierNat hValid.toOrdered hWidth) packet.pair.u.1.val
    ∃ event, event < F.lastEvent ∧ F.eventCut (event + 1) = F.height packet.pair.uUpper ∧
      (Forests.DepthWordLe forests (event + 1) F.lastEvent packet.pair.u.1.val packet.pair.z.1.val ↔
        F.value packet.pair.u ≤ F.value packet.pair.z) := by
  obtain ⟨event, hEvent, hCut, _, _, _, _, _, _, _, hCompare⟩ :=
    expandDiagram_common_raw_parent_depthWord hLegal hRun packet.pair.u_real packet.pair.z_real
      packet.pair.z_column packet.pair.u_parent packet.pair.z_parent packet.pair.u_upper packet.pair.z_upper
      packet.pair.upper_height hLeft hHigh (bottomCandidateMap packet.pair.u.1.val)
  exact ⟨event, hEvent, hCut, hCompare⟩

end SourceBlockerCopyPacket

end OmegaY.Expansion

#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.source_depth_word
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.target_depth_word_comparison
