/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualAnyLastBlocker.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAnyCommonParentPair
import OmegaY.Expansion.SourceLastBlocker
import OmegaY.Expansion.CommonRawParentDepthWord

/-!
# Every source last-blocker comparison branch in an actual recorded copy

Source search selects the blocker. The actual history constructs its target
comparison packet whether the blocker stays in the original prefix or is
copied, and whether the common father is fixed, a root endpoint or copied.
The source inequality and the target comparison event are both obtained.
Their missing depth-word transport and the new Q-chain identification are
not assumed and are not concluded by this interface.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

structure AnySourceBlockerPacket {front : List Nat} {last : Nat}
    (p : Preparation front last) (block : Nat) (start : Mountain) (references : List Ref)
    (sourceU sourceParent : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  candidate : (Frame.ofMountain p.reduced).Node
  blocker : (Frame.ofMountain p.reduced).Node
  sourceUUpper : (Frame.ofMountain p.reduced).Node
  sourceZUpper : (Frame.ofMountain p.reduced).Node
  source_candidate : (Frame.ofMountain p.reduced).Q sourceU = some candidate
  source_parent : (Frame.ofMountain p.reduced).P sourceU = some sourceParent
  source_path : ParentPath (Frame.ofMountain p.reduced) candidate blocker
  source_last_parent : (Frame.ofMountain p.reduced).P blocker = some sourceParent
  blocker_before : blocker.1.val < sourceU.1.val
  source_u_upper : (Frame.ofMountain p.reduced).upper sourceU = some sourceUUpper
  source_z_upper : (Frame.ofMountain p.reduced).upper blocker = some sourceZUpper
  source_lower : (Frame.ofMountain p.reduced).height blocker ≤ (Frame.ofMountain p.reduced).height sourceU
  source_overlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper
  source_upper_height : (Frame.ofMountain p.reduced).height sourceUUpper = (Frame.ofMountain p.reduced).height sourceZUpper
  source_value : (Frame.ofMountain p.reduced).value sourceU ≤ (Frame.ofMountain p.reduced).value blocker
  pair : AnyCommonParentPair p block start references sourceU blocker sourceParent result

theorem DynamicBlockState.recorded_any_last_blocker
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hRight : p.root.column < sourceU.1.val) (hBefore : sourceU.1.val < next) :
    (Frame.ofMountain p.reduced).Q sourceU = some sourceParent ∨
      Nonempty (AnySourceBlockerPacket p block start references sourceU sourceParent ambient) := by
  obtain ⟨q, hQ, hDirect | ⟨z, uUpper, zUpper, hPath, hLastParent, _, hZBefore,
      hUUpper, hZUpper, hLower, hOverlap, hUpperHeight, hValue, _⟩⟩ :=
    build_source_last_blocker p.reduced_build hParent
  · exact Or.inl (hDirect ▸ hQ)
  · obtain ⟨pair⟩ := s.recorded_any_common_parent_pair history hLast hStartRun hParent hLastParent
      hRight hZBefore.le hBefore hZUpper hLower hOverlap
    exact Or.inr ⟨{
      candidate := q, blocker := z, sourceUUpper := uUpper, sourceZUpper := zUpper
      source_candidate := hQ, source_parent := hParent, source_path := hPath
      source_last_parent := hLastParent, blocker_before := hZBefore
      source_u_upper := hUUpper, source_z_upper := hZUpper
      source_lower := hLower, source_overlap := hOverlap, source_upper_height := hUpperHeight
      source_value := hValue, pair := pair }⟩

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent result)

theorem source_depth_word :
    let F := Frame.ofMountain p.reduced
    let hN := build_normal_of_success p.reduced_build
    let hWidth := (Nat.zero_le sourceU.1.val).trans_lt sourceU.1.isLt
    let forests := F.frontierForests (bottomCandidateMap sourceU.1.val)
      (eventFrontierNat hN.toOrdered hWidth) sourceU.1.val
    ∃ event, event < F.lastEvent ∧ F.eventCut (event + 1) = F.height packet.sourceUUpper ∧
      Forests.DepthWordLe forests (event + 1) F.lastEvent sourceU.1.val packet.blocker.1.val := by
  have hWidth : 0 < p.reduced.size := (Nat.zero_le sourceU.1.val).trans_lt sourceU.1.isLt
  obtain ⟨uUpper, event, hUpper, hEvent, _, hCut, _, _, _, _, hCompare⟩ :=
    build_common_parent_upper_depthWord p.reduced_build hWidth sourceU.1.isLt le_rfl packet.blocker_before.le
      packet.source_parent packet.source_last_parent packet.source_z_upper packet.source_lower packet.source_overlap
  have he : uUpper = packet.sourceUUpper := Option.some.inj (hUpper.symm.trans packet.source_u_upper)
  exact ⟨event, hEvent, he ▸ hCut, hCompare.mpr packet.source_value⟩

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

end AnySourceBlockerPacket

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_any_last_blocker
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.source_depth_word
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.target_depth_word_comparison
