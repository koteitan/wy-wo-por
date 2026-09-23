/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighPhysicalRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighBlockerRecognition
import OmegaY.Expansion.ActualPhysicalStationaryIdentity

/-!
# High-upper numerical recognition at physical marker occurrences

The high source upper forces physical/effective identity at the current
marker. Existing high-upper recognition therefore applies at that exact
physical node. The actual physical raw edge then identifies its parent
with the packet's effective parent by single-valuedness of rawParent.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace SourceBlockerCopyPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source parent : (Frame.ofMountain p.reduced).Node}
  (packet : SourceBlockerCopyPacket p block start references source parent result)
  (physical : PhysicalMarkerRead packet.pair.uCopy)

theorem recognize_high_physical_upper
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    (hParentRight : p.root.column < parent.1.val)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height packet.sourceUUpper)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Frame.Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (hHigher : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Frame.Real node → (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father) :
    findParent result physical.outputRef = .ok packet.pair.parentCopy.outputRef := by
  have hIdentity := (physical.high_upper_eq_effective hLast hMarked packet.source_u_upper hHigh).1
  have hP := packet.recognize_high_upper hLast hLegal hCopies hRun hParentRight hHigh hLeft hHigher
  have hSearch := (Executable.findParent_ref_iff (expandDiagram_valid_of_success hLegal hRun).toOrdered
    packet.pair.u packet.pair.parent).mpr hP
  simpa only [hIdentity, packet.pair.u_ref, packet.pair.parent_ref] using hSearch

include physical in
theorem high_physical_parent_eq_effective
    (hLast : 1 < last) (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    (hParentRight : p.root.column < parent.1.val)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height packet.sourceUUpper)
    (parentPhysical : PhysicalMarkerRead packet.pair.parentCopy) :
    parentPhysical.outputRef = packet.pair.parentCopy.outputRef := by
  have hIdentity := (physical.high_upper_eq_effective hLast hMarked packet.source_u_upper hHigh).1
  obtain ⟨actualParent, hParentRef, _⟩ := Canonical.frame_node_of_cellAt parentPhysical.output_read
  have hRaw := (physical.raw_parent hLast hValid hMarked parentPhysical packet.source_parent hParentRight).1.rawParent
    (packet.pair.u_ref.trans hIdentity.symm) hParentRef
  have he : actualParent = packet.pair.parent := Option.some.inj (hRaw.symm.trans packet.pair.u_parent)
  exact hParentRef.symm.trans ((congrArg Frame.ref he).trans packet.pair.parent_ref)

/-- Both endpoints in this conclusion are the actual physical occurrences.
The induction hypotheses are about the packet's current node, which is
proved to be precisely the given physical current node. -/
theorem recognize_high_physical_parent
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    (hParentRight : p.root.column < parent.1.val)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height packet.sourceUUpper)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Frame.Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (hHigher : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Frame.Real node → (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (parentPhysical : PhysicalMarkerRead packet.pair.parentCopy) :
    findParent result physical.outputRef = .ok parentPhysical.outputRef := by
  have hParentRef := packet.high_physical_parent_eq_effective physical hLast
    (expandDiagram_valid_of_success hLegal hRun) hMarked hParentRight hHigh parentPhysical
  rw [hParentRef]
  exact packet.recognize_high_physical_upper physical hLast hLegal hCopies hRun hMarked hParentRight hHigh hLeft hHigher

end SourceBlockerCopyPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.recognize_high_physical_upper
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.high_physical_parent_eq_effective
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.recognize_high_physical_parent
