/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedAnyLastBlocker.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAnyLastBlocker
import OmegaY.Expansion.PreservedAnyCommonParentPair

/-!
# Last-blocker source data and actual comparison nodes in later prefixes

Complete columns preserve all source correspondence and actual parent edges.
Later event enumerations are rebuilt; an old event number is not reused.
The target numerical barrier is still a separate obligation.
-/

namespace OmegaY.Expansion

open Canonical Geometry

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start before after : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent before)
  (h : PreservesColumns before after)

noncomputable def extend :
    AnySourceBlockerPacket p block start references sourceU sourceParent after :=
  { packet with pair := packet.pair.extend h }

theorem extend_values :
    (Frame.ofMountain after).value (packet.extend h).pair.u =
        (Frame.ofMountain before).value packet.pair.u ∧
      (Frame.ofMountain after).value (packet.extend h).pair.z =
        (Frame.ofMountain before).value packet.pair.z :=
  packet.pair.extend_values h

theorem extend_barrier_iff :
    (Frame.ofMountain after).value (packet.extend h).pair.u ≤
        (Frame.ofMountain after).value (packet.extend h).pair.z ↔
      (Frame.ofMountain before).value packet.pair.u ≤
        (Frame.ofMountain before).value packet.pair.z := by
  rw [(packet.extend_values h).1, (packet.extend_values h).2]

end AnySourceBlockerPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.AnySourceBlockerPacket.extend
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.extend_values
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.extend_barrier_iff
