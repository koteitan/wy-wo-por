/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLastBlockerPair.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentPacket
import OmegaY.Expansion.SourceLastBlocker
import OmegaY.Expansion.CommonMarkerBlocker
import OmegaY.Expansion.ActualEffectivePaths
import OmegaY.Expansion.ActualMarkedCommonParentPacket

/-!
# Actual copies of the source search's last blocker

The source search itself selects the last blocker and its overlap. Source
marker equivalence determines its unmarked branch. The real recorded copy
then supplies a common-parent comparison packet and the copied source record
path from the source candidate's effective occurrence. This does not identify the
selected source blocker with the last blocker of the new output Q chain,
or transport its numerical inequality; those are still separate obligations.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem marked_index_iff {front : List Nat} {last : Nat}
    (p : Preparation front last) (node : (Frame.ofMountain p.reduced).Node) :
    node.2.val ∈ (p.marked[node.1.val]?.getD []).map Ref.index ↔
      BucketMem p.marked node.1.val (Frame.ref node) := by
  constructor
  · intro h
    obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
    have hc := (p.marker_iff.mp hm).1
    have he : marker = Frame.ref node := by
      cases marker
      simp only [Frame.ref, Ref.mk.injEq]
      exact ⟨hc, hi⟩
    exact he ▸ hm
  · intro h
    exact List.mem_map.mpr ⟨Frame.ref node, h, rfl⟩

structure SourceBlockerCopyPacket {front : List Nat} {last : Nat}
    (p : Preparation front last) (block : Nat) (start : Mountain) (references : List Ref)
    (sourceU sourceParent : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  candidate : (Frame.ofMountain p.reduced).Node
  blocker : (Frame.ofMountain p.reduced).Node
  sourceUUpper : (Frame.ofMountain p.reduced).Node
  sourceZUpper : (Frame.ofMountain p.reduced).Node
  source_candidate : (Frame.ofMountain p.reduced).Q sourceU = some candidate
  source_parent : (Frame.ofMountain p.reduced).P sourceU = some sourceParent
  source_path : Frame.ParentPath (Frame.ofMountain p.reduced) candidate blocker
  source_last_parent : (Frame.ofMountain p.reduced).P blocker = some sourceParent
  blocker_before : blocker.1.val < sourceU.1.val
  source_u_upper : (Frame.ofMountain p.reduced).upper sourceU = some sourceUUpper
  source_z_upper : (Frame.ofMountain p.reduced).upper blocker = some sourceZUpper
  source_lower : (Frame.ofMountain p.reduced).height blocker ≤ (Frame.ofMountain p.reduced).height sourceU
  source_overlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper
  source_upper_height : (Frame.ofMountain p.reduced).height sourceUUpper = (Frame.ofMountain p.reduced).height sourceZUpper
  source_value : (Frame.ofMountain p.reduced).value sourceU ≤ (Frame.ofMountain p.reduced).value blocker
  source_upper_value : (Frame.ofMountain p.reduced).value sourceUUpper ≤ (Frame.ofMountain p.reduced).value sourceZUpper
  pair : EffectiveCommonParentPair p block start references sourceU blocker sourceParent result
  candidateCopy : EffectiveCopyOccurrence p block start references candidate result
  copied_record_path : RawRefPath result candidateCopy.outputRef pair.zCopy.outputRef

/-- The blocker, source inequalities, branch membership and all target
comparison nodes are constructed. Only the current source-parent equation
and its unmarked/right-parent branch are supplied. -/
theorem DynamicBlockState.recorded_nonmarker_last_blocker
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hParentRight : p.root.column < sourceParent.1.val) (hBefore : sourceU.1.val < next)
    (hUnmarked : sourceU.2.val ∉ (p.marked[sourceU.1.val]?.getD []).map Ref.index) :
    (Frame.ofMountain p.reduced).Q sourceU = some sourceParent ∨
      Nonempty (SourceBlockerCopyPacket p block start references sourceU sourceParent ambient) := by
  obtain ⟨q, hQ, hDirect | ⟨z, uUpper, zUpper, hPath, hLastParent, _, hZBefore,
      hUUpper, hZUpper, hLower, hOverlap, hUpperHeight, hValue, hUpperValue⟩⟩ :=
    build_source_last_blocker p.reduced_build hParent
  · exact Or.inl (hDirect ▸ hQ)
  · obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
    have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
      simpa only [hRootRef] using p.markers_built
    have hRootColumn : root.1.val = p.root.column := congrArg Ref.column hRootRef
    have hIff := build_common_parent_marker_iff p.reduced_build hMarkers hParent hLastParent
      hZUpper hLower hOverlap (hRootColumn.trans_le hParentRight.le)
    have hZUnmarked : z.2.val ∉ (p.marked[z.1.val]?.getD []).map Ref.index := by
      intro hm
      exact hUnmarked ((marked_index_iff p sourceU).mpr (hIff.mpr ((marked_index_iff p z).mp hm)))
    obtain ⟨pair⟩ := s.recorded_effective_common_parent_pair history hLast hParent hLastParent
      hParentRight hZBefore.le hBefore hUnmarked hZUnmarked hZUpper hLower hOverlap
    have hNormal := build_normal_of_success p.reduced_build
    have hZRight := hParentRight.trans (Frame.P_column_lt hNormal.toOrdered hLastParent)
    have hQBefore := (Frame.Q_column_lt hNormal.toOrdered hQ).trans hBefore
    obtain ⟨candidateCopy⟩ := s.prior_effective_occurrence history hLast
      (hZRight.trans_le (hPath.column_le hNormal.toOrdered)) hQBefore
    have hCopiedPath := s.recorded_effective_path history hLast hPath hZRight hQBefore candidateCopy pair.zCopy
    exact Or.inr ⟨{
      candidate := q, blocker := z, sourceUUpper := uUpper, sourceZUpper := zUpper
      source_candidate := hQ, source_parent := hParent, source_path := hPath, source_last_parent := hLastParent
      blocker_before := hZBefore, source_u_upper := hUUpper, source_z_upper := hZUpper
      source_lower := hLower, source_overlap := hOverlap, source_upper_height := hUpperHeight
      source_value := hValue, source_upper_value := hUpperValue, pair := pair
      candidateCopy := candidateCopy, copied_record_path := hCopiedPath }⟩

/-- Both source marker branches are handled internally. The complete
actual outer prefix supplies the raw geometry used in the marked case.
The copied path starts at the source candidate's effective occurrence;
equality with the new numerical Q candidate is deliberately not asserted. -/
theorem DynamicBlockState.recorded_last_blocker
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
    (hParentRight : p.root.column < sourceParent.1.val) (hBefore : sourceU.1.val < next) :
    (Frame.ofMountain p.reduced).Q sourceU = some sourceParent ∨
      Nonempty (SourceBlockerCopyPacket p block start references sourceU sourceParent ambient) := by
  obtain ⟨q, hQ, hDirect | ⟨z, uUpper, zUpper, hPath, hLastParent, _, hZBefore,
      hUUpper, hZUpper, hLower, hOverlap, hUpperHeight, hValue, hUpperValue⟩⟩ :=
    build_source_last_blocker p.reduced_build hParent
  · exact Or.inl (hDirect ▸ hQ)
  · obtain ⟨pair⟩ := s.recorded_common_parent_pair history hLast hStartRun hParent hLastParent
      hParentRight hZBefore.le hBefore hZUpper hLower hOverlap
    have hNormal := build_normal_of_success p.reduced_build
    have hZRight := hParentRight.trans (Frame.P_column_lt hNormal.toOrdered hLastParent)
    have hQBefore := (Frame.Q_column_lt hNormal.toOrdered hQ).trans hBefore
    obtain ⟨candidateCopy⟩ := s.prior_effective_occurrence history hLast
      (hZRight.trans_le (hPath.column_le hNormal.toOrdered)) hQBefore
    have hCopiedPath := s.recorded_effective_path history hLast hPath hZRight hQBefore candidateCopy pair.zCopy
    exact Or.inr ⟨{
      candidate := q, blocker := z, sourceUUpper := uUpper, sourceZUpper := zUpper
      source_candidate := hQ, source_parent := hParent, source_path := hPath, source_last_parent := hLastParent
      blocker_before := hZBefore, source_u_upper := hUUpper, source_z_upper := hZUpper
      source_lower := hLower, source_overlap := hOverlap, source_upper_height := hUpperHeight
      source_value := hValue, source_upper_value := hUpperValue, pair := pair
      candidateCopy := candidateCopy, copied_record_path := hCopiedPath }⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_nonmarker_last_blocker
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_last_blocker
