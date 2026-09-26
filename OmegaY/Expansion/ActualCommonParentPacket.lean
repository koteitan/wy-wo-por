/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCommonParentPacket.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentUpper
import OmegaY.Expansion.RecordedEffectiveEdges
import OmegaY.Expansion.CommonRawParentDepthWord

/-!
# A common-parent comparison packet constructed from recorded copies

For two unmarked source records with a strictly-right common father, the
actual history determines both effective nodes, their identical stored
father, and their equally high immediate uppers. All these target facts are
constructed, not caller-supplied output geometry. Numerical recognition and
the source-to-target depth-word inequality remain separate.
-/

namespace OmegaY.Expansion

open Canonical Geometry

structure EffectiveCommonParentPair {front : List Nat} {last : Nat}
    (p : Preparation front last) (block : Nat) (start : Mountain) (references : List Ref)
    (sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  uCopy : EffectiveCopyOccurrence p block start references sourceU result
  zCopy : EffectiveCopyOccurrence p block start references sourceZ result
  parentCopy : EffectiveCopyOccurrence p block start references sourceParent result
  u : (Frame.ofMountain result).Node
  z : (Frame.ofMountain result).Node
  parent : (Frame.ofMountain result).Node
  uUpper : (Frame.ofMountain result).Node
  zUpper : (Frame.ofMountain result).Node
  u_ref : Frame.ref u = uCopy.outputRef
  z_ref : Frame.ref z = zCopy.outputRef
  parent_ref : Frame.ref parent = parentCopy.outputRef
  u_real : Frame.Real u
  z_real : Frame.Real z
  z_column : z.1.val ≤ u.1.val
  u_parent : (Frame.ofMountain result).rawParent u = some parent
  z_parent : (Frame.ofMountain result).rawParent z = some parent
  u_upper : (Frame.ofMountain result).upper u = some uUpper
  z_upper : (Frame.ofMountain result).upper z = some zUpper
  upper_height : (Frame.ofMountain result).height uUpper = (Frame.ofMountain result).height zUpper

/-- All target fields of the comparison packet are consequences of the
actual history and the overlapping common-parent source records. -/
theorem DynamicBlockState.recorded_effective_common_parent_pair
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceU sourceZ sourceParent sourceZUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hZP : (Frame.ofMountain p.reduced).P sourceZ = some sourceParent)
    (hParentRight : p.root.column < sourceParent.1.val)
    (hZColumn : sourceZ.1.val ≤ sourceU.1.val) (hBefore : sourceU.1.val < next)
    (hUUnmarked : sourceU.2.val ∉ (p.marked[sourceU.1.val]?.getD []).map Ref.index)
    (hZUnmarked : sourceZ.2.val ∉ (p.marked[sourceZ.1.val]?.getD []).map Ref.index)
    (hZUpper : (Frame.ofMountain p.reduced).upper sourceZ = some sourceZUpper)
    (hOrder : (Frame.ofMountain p.reduced).height sourceZ ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hOverlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper) :
    Nonempty (EffectiveCommonParentPair p block start references sourceU sourceZ sourceParent ambient) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hUParentLeft := Frame.P_column_lt hNormal.toOrdered hUP
  have hZParentLeft := Frame.P_column_lt hNormal.toOrdered hZP
  obtain ⟨uCopy⟩ := s.prior_effective_occurrence history hLast (hParentRight.trans hUParentLeft) hBefore
  obtain ⟨zCopy⟩ := s.prior_effective_occurrence history hLast (hParentRight.trans hZParentLeft) (hZColumn.trans_lt hBefore)
  obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hParentRight (hUParentLeft.trans hBefore)
  have hUEdge := s.recorded_effective_parent history hLast hUP hParentRight hBefore uCopy parentCopy
  have hZEdge := s.recorded_effective_parent history hLast hZP hParentRight (hZColumn.trans_lt hBefore) zCopy parentCopy
  obtain ⟨uUpperCell, zUpperCell, hUUpperRead, hZUpperRead, hRows⟩ :=
    uCopy.common_parent_upper_rows_of_overlap zCopy hLast hUUnmarked hZUnmarked hUP hZP hZUpper hOrder hOverlap
  obtain ⟨u, hURef, _⟩ := Canonical.frame_node_of_cellAt uCopy.output_read
  obtain ⟨z, hZRef, _⟩ := Canonical.frame_node_of_cellAt zCopy.output_read
  obtain ⟨parent, hParentRef, _⟩ := Canonical.frame_node_of_cellAt parentCopy.output_read
  obtain ⟨uUpper, hUUpperRef, hUUpperCell⟩ := Canonical.frame_node_of_cellAt hUUpperRead
  obtain ⟨zUpper, hZUpperRef, hZUpperCell⟩ := Canonical.frame_node_of_cellAt hZUpperRead
  have hUSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hUP).1.trans (Frame.P_value hNormal.toOrdered hUP).2)
  have hZSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hZP).1.trans (Frame.P_value hNormal.toOrdered hZP).2)
  refine ⟨{
    uCopy := uCopy, zCopy := zCopy, parentCopy := parentCopy
    u := u, z := z, parent := parent, uUpper := uUpper, zUpper := zUpper
    u_ref := hURef, z_ref := hZRef, parent_ref := hParentRef
    u_real := ?_, z_real := ?_, z_column := ?_
    u_parent := hUEdge.rawParent hURef hParentRef
    z_parent := hZEdge.rawParent hZRef hParentRef
    u_upper := Frame.upper_of_refs hURef hUUpperRef
    z_upper := Frame.upper_of_refs hZRef hZUpperRef
    upper_height := (congrArg Cell.row hUUpperCell).trans (hRows.trans (congrArg Cell.row hZUpperCell).symm) }⟩
  · have hIndex := congrArg Ref.index hURef
    change u.2.val = uCopy.read.outputIndex at hIndex
    change 0 < u.2.val
    rw [hIndex]
    exact uCopy.read.output_real hUSourceReal
  · have hIndex := congrArg Ref.index hZRef
    change z.2.val = zCopy.read.outputIndex at hIndex
    change 0 < z.2.val
    rw [hIndex]
    exact zCopy.read.output_real hZSourceReal
  · have hUColumn := (congrArg Ref.column hURef).trans uCopy.source_column
    have hZColumn' := (congrArg Ref.column hZRef).trans zCopy.source_column
    change u.1.val = _ at hUColumn
    change z.1.val = _ at hZColumn'
    omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_effective_common_parent_pair
