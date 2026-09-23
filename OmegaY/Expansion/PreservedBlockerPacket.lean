/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedBlockerPacket.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualBlockerDepthWords
import OmegaY.Expansion.PreservedFrameNodes

/-!
# Recorded comparison packets in later complete-prefix extensions

Later blocks add events but preserve earlier complete columns. The actual
copies, full node values, stored common parents and source record paths
therefore survive. The later graph must use its own event enumeration;
this does not claim that old event indices remain unchanged.
-/

namespace OmegaY.Expansion

open Canonical Geometry

noncomputable def EffectiveCommonParentPair.extend
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start before after : Mountain} {references : List Ref}
    {sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node}
    (pair : EffectiveCommonParentPair p block start references sourceU sourceZ sourceParent before)
    (h : PreservesColumns before after) :
    EffectiveCommonParentPair p block start references sourceU sourceZ sourceParent after where
  uCopy := pair.uCopy.extend h
  zCopy := pair.zCopy.extend h
  parentCopy := pair.parentCopy.extend h
  u := h.mapNode pair.u
  z := h.mapNode pair.z
  parent := h.mapNode pair.parent
  uUpper := h.mapNode pair.uUpper
  zUpper := h.mapNode pair.zUpper
  u_ref := (h.mapNode_ref pair.u).trans pair.u_ref
  z_ref := (h.mapNode_ref pair.z).trans pair.z_ref
  parent_ref := (h.mapNode_ref pair.parent).trans pair.parent_ref
  u_real := h.mapNode_real pair.u_real
  z_real := h.mapNode_real pair.z_real
  z_column := by simpa only [h.mapNode_column] using pair.z_column
  u_parent := h.mapNode_rawParent pair.u_parent
  z_parent := h.mapNode_rawParent pair.z_parent
  u_upper := h.mapNode_upper pair.u_upper
  z_upper := h.mapNode_upper pair.z_upper
  upper_height := by simpa only [h.mapNode_height] using pair.upper_height

theorem EffectiveCommonParentPair.extend_values
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start before after : Mountain} {references : List Ref}
    {sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node}
    (pair : EffectiveCommonParentPair p block start references sourceU sourceZ sourceParent before)
    (h : PreservesColumns before after) :
    (Frame.ofMountain after).value (pair.extend h).u = (Frame.ofMountain before).value pair.u ∧
      (Frame.ofMountain after).value (pair.extend h).z = (Frame.ofMountain before).value pair.z :=
  ⟨congrArg Cell.value (h.mapNode_cell pair.u), congrArg Cell.value (h.mapNode_cell pair.z)⟩

noncomputable def SourceBlockerCopyPacket.extend
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start before after : Mountain} {references : List Ref}
    {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
    (packet : SourceBlockerCopyPacket p block start references sourceU sourceParent before)
    (h : PreservesColumns before after) :
    SourceBlockerCopyPacket p block start references sourceU sourceParent after :=
  { packet with
    pair := packet.pair.extend h
    candidateCopy := packet.candidateCopy.extend h
    copied_record_path := packet.copied_record_path.preserve h }

theorem SourceBlockerCopyPacket.extend_values
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start before after : Mountain} {references : List Ref}
    {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
    (packet : SourceBlockerCopyPacket p block start references sourceU sourceParent before)
    (h : PreservesColumns before after) :
    (Frame.ofMountain after).value (packet.extend h).pair.u = (Frame.ofMountain before).value packet.pair.u ∧
      (Frame.ofMountain after).value (packet.extend h).pair.z = (Frame.ofMountain before).value packet.pair.z :=
  packet.pair.extend_values h

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCommonParentPair.extend
#print axioms OmegaY.Expansion.EffectiveCommonParentPair.extend_values
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.extend
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.extend_values
