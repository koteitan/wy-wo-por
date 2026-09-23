/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCopiedBlockerCandidate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualUnmarkedCandidate
import OmegaY.Expansion.ActualAnyLastBlocker
import OmegaY.Expansion.ActualFixedSourceValue

/-!
# A copied last blocker excludes a marked first source candidate

Along a real source parent path ending strictly right of the root, marker
membership propagates. A last blocker whose parent is in the good part
cannot be marked. Thus its preceding source candidate is also unmarked;
its physical and effective alternatives need not be guessed.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem Preparation.marked_at_parent_path_right
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {child endpoint : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) child endpoint)
    (hMarked : BucketMem p.marked child.1.val (Frame.ref child))
    (hRight : p.root.column < endpoint.1.val) :
    BucketMem p.marked endpoint.1.val (Frame.ref endpoint) := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  induction path with
  | refl _ => exact hMarked
  | @cons child middle endpoint hEdge tail ih =>
    have hMiddleRight := hRight.trans_le (tail.column_le hNormal.toOrdered)
    have hMiddleMarked := (build_marked_parent p.reduced_build hMarkers hEdge hMarked
      ((congrArg Ref.column hRootRef).trans_lt hMiddleRight)).1
    exact ih hMiddleMarked hRight

theorem AnySourceBlockerPacket.candidate_unmarked_of_copied_fixed_blocker
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source parent : (Frame.ofMountain p.reduced).Node}
    (packet : AnySourceBlockerPacket p block start references source parent result)
    (hFixed : parent.1.val < p.root.column)
    (hRight : p.root.column < packet.blocker.1.val) :
    packet.candidate.2.val ∉ (p.marked[packet.candidate.1.val]?.getD []).map Ref.index := by
  intro hMarkedIndex
  obtain ⟨marker, hm, hi⟩ := List.mem_map.mp hMarkedIndex
  have hRef : marker = Frame.ref packet.candidate :=
    congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
  have hMarked : BucketMem p.marked packet.candidate.1.val (Frame.ref packet.candidate) := hRef ▸ hm
  exact p.fixed_parent_not_marked packet.source_last_parent hFixed
    (p.marked_at_parent_path_right packet.source_path hMarked hRight)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.marked_at_parent_path_right
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.candidate_unmarked_of_copied_fixed_blocker
