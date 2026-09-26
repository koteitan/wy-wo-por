/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkedCommonParentPacket.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentPacket
import OmegaY.Expansion.HistoryRawInvariants
import OmegaY.Expansion.CommonMarkerBlocker

/-!
# Actual common-parent packets for marked and unmarked sources

In the marked branch the source overlap makes both source nodes marked
at the same row. Their real reference queries use the same block-start
map, so their effective rows coincide. Actual recorded parent edges and
executed raw row geometry then force their immediate uppers to coincide
in height as well. This is a target packet construction, not numerical
parent recognition or an assumed target comparison.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem source_marked_index_iff {front : List Nat} {last : Nat}
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

/-- Either marked source supplies the marked case. All effective reads,
common raw parents, and upper rows are constructed from actual execution. -/
theorem DynamicBlockState.recorded_marked_common_parent_pair
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {sourceU sourceZ sourceParent sourceZUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hZP : (Frame.ofMountain p.reduced).P sourceZ = some sourceParent)
    (hParentRight : p.root.column < sourceParent.1.val)
    (hZColumn : sourceZ.1.val ≤ sourceU.1.val) (hBefore : sourceU.1.val < next)
    (hZUpper : (Frame.ofMountain p.reduced).upper sourceZ = some sourceZUpper)
    (hOrder : (Frame.ofMountain p.reduced).height sourceZ ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hOverlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper)
    (hMarked : BucketMem p.marked sourceU.1.val (Frame.ref sourceU) ∨
      BucketMem p.marked sourceZ.1.val (Frame.ref sourceZ)) :
    Nonempty (EffectiveCommonParentPair p block start references sourceU sourceZ sourceParent ambient) := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  have hRootColumn : root.1.val = p.root.column := congrArg Ref.column hRootRef
  obtain ⟨hUMarked, hZMarked, hURow, hZRow, _⟩ :=
    build_common_parent_marker_rows p.reduced_build hMarkers hUP hZP hZUpper hOrder hOverlap
      (hRootColumn.trans_le hParentRight.le) hMarked
  have hUParentLeft := Frame.P_column_lt hNormal.toOrdered hUP
  have hZParentLeft := Frame.P_column_lt hNormal.toOrdered hZP
  obtain ⟨uCopy⟩ := s.prior_effective_occurrence history hLast (hParentRight.trans hUParentLeft) hBefore
  obtain ⟨zCopy⟩ := s.prior_effective_occurrence history hLast (hParentRight.trans hZParentLeft)
    (hZColumn.trans_lt hBefore)
  obtain ⟨parentCopy⟩ := s.prior_effective_occurrence history hLast hParentRight
    (hUParentLeft.trans hBefore)
  have hUReference : referenceAt start references (F.height sourceU) = .ok uCopy.read.outputCell.row :=
    (uCopy.state.referenceAt_preserved _).symm.trans (uCopy.read.marked_reference hUMarked)
  have hZReference : referenceAt start references (F.height sourceZ) = .ok zCopy.read.outputCell.row :=
    (zCopy.state.referenceAt_preserved _).symm.trans (zCopy.read.marked_reference hZMarked)
  change F.height sourceU = F.height sourceParent at hURow
  change F.height sourceZ = F.height sourceParent at hZRow
  rw [hURow] at hUReference
  rw [hZRow] at hZReference
  have hLowerRows : uCopy.read.outputCell.row = zCopy.read.outputCell.row :=
    Except.ok.inj (hUReference.symm.trans hZReference)
  have hUEdge := s.recorded_effective_parent history hLast hUP hParentRight hBefore uCopy parentCopy
  have hZEdge := s.recorded_effective_parent history hLast hZP hParentRight
    (hZColumn.trans_lt hBefore) zCopy parentCopy
  have hUHasUpper : ∃ cell, Canonical.cellAt ambient
      ⟨uCopy.outputRef.column, uCopy.outputRef.index + 1⟩ = .ok cell := by
    obtain ⟨_, upper, _, _, hRead, _, _⟩ := hUEdge
    exact ⟨upper, hRead⟩
  have hZHasUpper : ∃ cell, Canonical.cellAt ambient
      ⟨zCopy.outputRef.column, zCopy.outputRef.index + 1⟩ = .ok cell := by
    obtain ⟨_, upper, _, _, hRead, _, _⟩ := hZEdge
    exact ⟨upper, hRead⟩
  obtain ⟨upperUCell, hUpperURead⟩ := hUHasUpper
  obtain ⟨upperZCell, hUpperZRead⟩ := hZHasUpper
  obtain ⟨u, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt uCopy.output_read
  obtain ⟨z, hZRef, hZCell⟩ := Canonical.frame_node_of_cellAt zCopy.output_read
  obtain ⟨parent, hParentRef, _⟩ := Canonical.frame_node_of_cellAt parentCopy.output_read
  obtain ⟨uUpper, hUUpperRef, _⟩ := Canonical.frame_node_of_cellAt hUpperURead
  obtain ⟨zUpper, hZUpperRef, _⟩ := Canonical.frame_node_of_cellAt hUpperZRead
  have hUSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hUP).1.trans (Frame.P_value hNormal.toOrdered hUP).2)
  have hZSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hZP).1.trans (Frame.P_value hNormal.toOrdered hZP).2)
  have hUReal : Frame.Real u := by
    have hi : u.2.val = uCopy.read.outputIndex := congrArg Ref.index hURef
    change 0 < u.2.val
    rw [hi]
    exact uCopy.read.output_real hUSourceReal
  have hZReal : Frame.Real z := by
    have hi : z.2.val = zCopy.read.outputIndex := congrArg Ref.index hZRef
    change 0 < z.2.val
    rw [hi]
    exact zCopy.read.output_real hZSourceReal
  have hUParent : T.rawParent u = some parent := hUEdge.rawParent hURef hParentRef
  have hZParent : T.rawParent z = some parent := hZEdge.rawParent hZRef hParentRef
  have hUUpper : T.upper u = some uUpper := Frame.upper_of_refs hURef hUUpperRef
  have hZUpper' : T.upper z = some zUpper := Frame.upper_of_refs hZRef hZUpperRef
  have hRaw := (s.raw_invariants_of_start_run history hLast hStartRun).1
  have hUpperB : T.height uUpper = Row.B (T.height u) (T.height parent) := by
    obtain ⟨actual, hActual, _, _, hB⟩ := hRaw u uUpper hUReal hUUpper
    have he : actual = parent := Option.some.inj (hActual.symm.trans hUParent)
    exact he ▸ hB
  have hZUpperB : T.height zUpper = Row.B (T.height z) (T.height parent) := by
    obtain ⟨actual, hActual, _, _, hB⟩ := hRaw z zUpper hZReal hZUpper'
    have he : actual = parent := Option.some.inj (hActual.symm.trans hZParent)
    exact he ▸ hB
  have hRows : T.height u = T.height z :=
    (congrArg Cell.row hUCell).trans (hLowerRows.trans (congrArg Cell.row hZCell).symm)
  refine ⟨{
    uCopy := uCopy, zCopy := zCopy, parentCopy := parentCopy
    u := u, z := z, parent := parent, uUpper := uUpper, zUpper := zUpper
    u_ref := hURef, z_ref := hZRef, parent_ref := hParentRef
    u_real := hUReal, z_real := hZReal, z_column := ?_
    u_parent := hUParent, z_parent := hZParent
    u_upper := hUUpper, z_upper := hZUpper'
    upper_height := hUpperB.trans ((congrArg (fun row => Row.B row (T.height parent)) hRows).trans hZUpperB.symm) }⟩
  have hUColumn := (congrArg Ref.column hURef).trans uCopy.source_column
  have hZColumn' := (congrArg Ref.column hZRef).trans zCopy.source_column
  change u.1.val = _ at hUColumn
  change z.1.val = _ at hZColumn'
  omega

/-- A complete common-parent packet for every overlapping pair with a
strictly-right source father. Marked/unmarked membership is decided inside
the theorem, and source marker equivalence determines the other node. -/
theorem DynamicBlockState.recorded_common_parent_pair
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {sourceU sourceZ sourceParent sourceZUpper : (Frame.ofMountain p.reduced).Node}
    (hUP : (Frame.ofMountain p.reduced).P sourceU = some sourceParent)
    (hZP : (Frame.ofMountain p.reduced).P sourceZ = some sourceParent)
    (hParentRight : p.root.column < sourceParent.1.val)
    (hZColumn : sourceZ.1.val ≤ sourceU.1.val) (hBefore : sourceU.1.val < next)
    (hZUpper : (Frame.ofMountain p.reduced).upper sourceZ = some sourceZUpper)
    (hOrder : (Frame.ofMountain p.reduced).height sourceZ ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hOverlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper) :
    Nonempty (EffectiveCommonParentPair p block start references sourceU sourceZ sourceParent ambient) := by
  by_cases hMarked : BucketMem p.marked sourceU.1.val (Frame.ref sourceU)
  · exact s.recorded_marked_common_parent_pair history hLast hStartRun hUP hZP hParentRight
      hZColumn hBefore hZUpper hOrder hOverlap (.inl hMarked)
  · obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
    have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
      simpa only [hRootRef] using p.markers_built
    have hRootColumn : root.1.val = p.root.column := congrArg Ref.column hRootRef
    have hIff := build_common_parent_marker_iff p.reduced_build hMarkers hUP hZP
      hZUpper hOrder hOverlap (hRootColumn.trans_le hParentRight.le)
    have hUUnmarked : sourceU.2.val ∉ (p.marked[sourceU.1.val]?.getD []).map Ref.index :=
      fun hm => hMarked ((source_marked_index_iff p sourceU).mp hm)
    have hZUnmarked : sourceZ.2.val ∉ (p.marked[sourceZ.1.val]?.getD []).map Ref.index :=
      fun hm => hMarked (hIff.mpr ((source_marked_index_iff p sourceZ).mp hm))
    exact s.recorded_effective_common_parent_pair history hLast hUP hZP hParentRight
      hZColumn hBefore hUUnmarked hZUnmarked hZUpper hOrder hOverlap

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_marked_common_parent_pair
#print axioms OmegaY.Expansion.DynamicBlockState.recorded_common_parent_pair
