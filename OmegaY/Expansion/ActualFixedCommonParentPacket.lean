/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFixedCommonParentPacket.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMixedCommonParentUpper

/-!
# Two effective copies with an unchanged good-part common parent

Both source nodes lie strictly right of the root and have actual effective
copies. Their common father stays at its original source reference. A good
father forces both sources to be unmarked, and their actual immediate
uppers retain their source heights even at physical-marker seams. Source
overlap supplies the shared upper height without a target row assumption.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem EffectiveCopyOccurrence.fixed_common_parent_upper_reads
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {sourceU sourceZ sourceParent sourceZUpper : (Frame.ofMountain p.reduced).Node}
    (uCopy : EffectiveCopyOccurrence p block start references sourceU result)
    (zCopy : EffectiveCopyOccurrence p block start references sourceZ result) (hLast : 1 < last)
    (hUP : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hZP : (Frame.ofMountain p.reduced).P sourceZ = some sourceParent)
    (hParentFixed : sourceParent.1.val < p.root.column)
    (hZUpper : (Frame.ofMountain p.reduced).upper sourceZ = some sourceZUpper)
    (hOrder : (Frame.ofMountain p.reduced).height sourceZ ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hOverlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper) :
    ∃ uUpper zUpper,
      Canonical.cellAt result ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok uUpper ∧
      Canonical.cellAt result ⟨zCopy.outputRef.column, zCopy.outputRef.index + 1⟩ = .ok zUpper ∧
      uUpper.row = zUpper.row := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨sourceUUpper, hUUpper⟩ := hNormal.upper_of_parent hUP
  obtain ⟨uUpper, hURead, hURow⟩ := uCopy.fixed_parent_upper_read hLast hUP hParentFixed hUUpper
  obtain ⟨zUpper, hZRead, hZRow⟩ := zCopy.fixed_parent_upper_read hLast hZP hParentFixed hZUpper
  have hSame := hNormal.common_parent_upper_rows hUP hZP hUUpper hZUpper hOrder hOverlap
  exact ⟨uUpper, zUpper, hURead, hZRead, hURow.trans (hSame.trans hZRow.symm)⟩

/-- Two actual copied endpoints and an unchanged source father. The father
is represented by its original reference and complete cell, never by a
fictitious effective copy in the fixed good part. -/
structure FixedCommonParentPair {front : List Nat} {last : Nat}
    (p : Preparation front last) (block : Nat) (start : Mountain) (references : List Ref)
    (sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  uCopy : EffectiveCopyOccurrence p block start references sourceU result
  zCopy : EffectiveCopyOccurrence p block start references sourceZ result
  u : (Frame.ofMountain result).Node
  z : (Frame.ofMountain result).Node
  parent : (Frame.ofMountain result).Node
  uUpper : (Frame.ofMountain result).Node
  zUpper : (Frame.ofMountain result).Node
  u_ref : Frame.ref u = uCopy.outputRef
  z_ref : Frame.ref z = zCopy.outputRef
  parent_ref : Frame.ref parent = Frame.ref sourceParent
  u_cell : (Frame.ofMountain result).cell u = uCopy.read.outputCell
  z_cell : (Frame.ofMountain result).cell z = zCopy.read.outputCell
  parent_cell : (Frame.ofMountain result).cell parent = (Frame.ofMountain p.reduced).cell sourceParent
  u_real : Frame.Real u
  z_real : Frame.Real z
  z_column : z.1.val ≤ u.1.val
  u_parent : (Frame.ofMountain result).rawParent u = some parent
  z_parent : (Frame.ofMountain result).rawParent z = some parent
  u_upper : (Frame.ofMountain result).upper u = some uUpper
  z_upper : (Frame.ofMountain result).upper z = some zUpper
  upper_height : (Frame.ofMountain result).height uUpper = (Frame.ofMountain result).height zUpper

/-- Actual history constructs both copies, their common unchanged stored
father, and equally high immediate uppers. Marker membership and all target
parent/row facts are conclusions rather than inputs. -/
theorem DynamicBlockState.recorded_fixed_common_parent_pair
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceU sourceZ sourceParent sourceZUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hZP : (Frame.ofMountain p.reduced).P sourceZ = some sourceParent)
    (hParentFixed : sourceParent.1.val < p.root.column)
    (hZRight : p.root.column < sourceZ.1.val)
    (hZColumn : sourceZ.1.val ≤ sourceU.1.val) (hBefore : sourceU.1.val < next)
    (hZUpper : (Frame.ofMountain p.reduced).upper sourceZ = some sourceZUpper)
    (hOrder : (Frame.ofMountain p.reduced).height sourceZ ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hOverlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper) :
    Nonempty (FixedCommonParentPair p block start references sourceU sourceZ sourceParent ambient) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hURight : p.root.column < sourceU.1.val := hZRight.trans_le hZColumn
  have hZBefore : sourceZ.1.val < next := hZColumn.trans_lt hBefore
  obtain ⟨uCopy⟩ := s.prior_effective_occurrence history hLast hURight hBefore
  obtain ⟨zCopy⟩ := s.prior_effective_occurrence history hLast hZRight hZBefore
  obtain ⟨hUEdge, hParentRead⟩ := s.recorded_fixed_parent history hLast hUP hURight hBefore hParentFixed uCopy
  have hZEdge := (s.recorded_fixed_parent history hLast hZP hZRight hZBefore hParentFixed zCopy).1
  obtain ⟨uUpperCell, zUpperCell, hUUpperRead, hZUpperRead, hRows⟩ :=
    uCopy.fixed_common_parent_upper_reads zCopy hLast hUP hZP hParentFixed hZUpper hOrder hOverlap
  obtain ⟨u, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt uCopy.output_read
  obtain ⟨z, hZRef, hZCell⟩ := Canonical.frame_node_of_cellAt zCopy.output_read
  obtain ⟨parent, hParentRef, hParentCell⟩ := Canonical.frame_node_of_cellAt hParentRead
  obtain ⟨uUpper, hUUpperRef, hUUpperCell⟩ := Canonical.frame_node_of_cellAt hUUpperRead
  obtain ⟨zUpper, hZUpperRef, hZUpperCell⟩ := Canonical.frame_node_of_cellAt hZUpperRead
  have hUSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hUP).1.trans (Frame.P_value hNormal.toOrdered hUP).2)
  have hZSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hZP).1.trans (Frame.P_value hNormal.toOrdered hZP).2)
  refine ⟨{
    uCopy := uCopy, zCopy := zCopy
    u := u, z := z, parent := parent, uUpper := uUpper, zUpper := zUpper
    u_ref := hURef, z_ref := hZRef, parent_ref := hParentRef
    u_cell := hUCell, z_cell := hZCell, parent_cell := hParentCell
    u_real := ?_, z_real := ?_, z_column := ?_
    u_parent := hUEdge.rawParent hURef hParentRef
    z_parent := hZEdge.rawParent hZRef hParentRef
    u_upper := Frame.upper_of_refs hURef hUUpperRef
    z_upper := Frame.upper_of_refs hZRef hZUpperRef
    upper_height := (congrArg Cell.row hUUpperCell).trans (hRows.trans (congrArg Cell.row hZUpperCell).symm) }⟩
  · have hi : u.2.val = uCopy.read.outputIndex := congrArg Ref.index hURef
    change 0 < u.2.val
    rw [hi]
    exact uCopy.read.output_real hUSourceReal
  · have hi : z.2.val = zCopy.read.outputIndex := congrArg Ref.index hZRef
    change 0 < z.2.val
    rw [hi]
    exact zCopy.read.output_real hZSourceReal
  · have hUColumn := (congrArg Ref.column hURef).trans uCopy.source_column
    have hZColumn' := (congrArg Ref.column hZRef).trans zCopy.source_column
    change u.1.val = _ at hUColumn
    change z.1.val = _ at hZColumn'
    omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.fixed_common_parent_upper_reads
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_fixed_common_parent_pair
