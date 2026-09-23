/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootCommonParentPacket.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRecordedRootParents
import OmegaY.Expansion.ActualCommonParentUpper
import OmegaY.Expansion.HistoryRawInvariants
import OmegaY.Expansion.CommonMarkerBlocker

/-!
# Complete actual comparison packets for a root-column common parent

The copy history supplies both effective children and their unique root
endpoint. In the nonmarker case, actual contour/marker-seam execution gives
common upper rows. In the marked case, source overlap forces a common
reference query and hence common effective lower rows; the already proved
raw row law then gives common upper rows. No copied numerical P or target
row equality is a premise.
-/

namespace OmegaY.Expansion

open Canonical Geometry

structure RootCommonParentPair {front : List Nat} {last : Nat}
    (p : Preparation front last) (block : Nat) (start : Mountain) (references : List Ref)
    (sourceU sourceZ sourceParent : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  uCopy : EffectiveCopyOccurrence p block start references sourceU result
  zCopy : EffectiveCopyOccurrence p block start references sourceZ result
  rootEndpoint : EffectiveRootEndpoint p start references sourceParent result
  u : (Frame.ofMountain result).Node
  z : (Frame.ofMountain result).Node
  parent : (Frame.ofMountain result).Node
  uUpper : (Frame.ofMountain result).Node
  zUpper : (Frame.ofMountain result).Node
  u_ref : Frame.ref u = uCopy.outputRef
  z_ref : Frame.ref z = zCopy.outputRef
  parent_ref : Frame.ref parent = rootEndpoint.reference
  u_real : Frame.Real u
  z_real : Frame.Real z
  z_column : z.1.val ≤ u.1.val
  u_parent : (Frame.ofMountain result).rawParent u = some parent
  z_parent : (Frame.ofMountain result).rawParent z = some parent
  u_upper : (Frame.ofMountain result).upper u = some uUpper
  z_upper : (Frame.ofMountain result).upper z = some zUpper
  upper_height : (Frame.ofMountain result).height uUpper = (Frame.ofMountain result).height zUpper

private theorem root_source_marked_index_iff {front : List Nat} {last : Nat}
    (p : Preparation front last) (node : (Frame.ofMountain p.reduced).Node) :
    node.2.val ∈ (p.marked[node.1.val]?.getD []).map Ref.index ↔
      BucketMem p.marked node.1.val (Frame.ref node) := by
  constructor
  · intro h
    obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
    have hc := (p.marker_iff.mp hm).1
    have he : marker = Frame.ref node := congrArg₂ Ref.mk hc hi
    exact he ▸ hm
  · intro h
    exact List.mem_map.mpr ⟨Frame.ref node, h, rfl⟩

/-- All packet fields come from actual source construction and recorded
copying. The two source nodes may both be marked or both be nonmarkers;
the caller supplies neither classification nor target same-row facts. -/
theorem DynamicBlockState.recorded_root_common_parent_pair
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
    (hRootColumn : sourceParent.1.val = p.root.column)
    (hZColumn : sourceZ.1.val ≤ sourceU.1.val) (hBefore : sourceU.1.val < next)
    (hZUpper : (Frame.ofMountain p.reduced).upper sourceZ = some sourceZUpper)
    (hOrder : (Frame.ofMountain p.reduced).height sourceZ ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hOverlap : (Frame.ofMountain p.reduced).height sourceU < (Frame.ofMountain p.reduced).height sourceZUpper) :
    Nonempty (RootCommonParentPair p block start references sourceU sourceZ sourceParent ambient) := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hUParentLeft := Frame.P_column_lt hNormal.toOrdered hUP
  have hZParentLeft := Frame.P_column_lt hNormal.toOrdered hZP
  have hURight : p.root.column < sourceU.1.val := hRootColumn ▸ hUParentLeft
  have hZRight : p.root.column < sourceZ.1.val := hRootColumn ▸ hZParentLeft
  obtain ⟨uCopy⟩ := s.prior_effective_occurrence history hLast hURight hBefore
  obtain ⟨zCopy⟩ := s.prior_effective_occurrence history hLast hZRight (hZColumn.trans_lt hBefore)
  obtain ⟨rootEndpoint, hUEdge, hZEdge⟩ := s.recorded_common_root_parent
    history hLast hStartRun hUP hZP hRootColumn hBefore (hZColumn.trans_lt hBefore) uCopy zCopy
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
  obtain ⟨parent, hParentRef, _⟩ := Canonical.frame_node_of_cellAt rootEndpoint.result_read
  obtain ⟨uUpper, hUUpperRef, hUUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperURead
  obtain ⟨zUpper, hZUpperRef, hZUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperZRead
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
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  have hRootLe : root.1.val ≤ sourceParent.1.val :=
    ((congrArg Ref.column hRootRef).trans hRootColumn.symm).le
  have hUpperRows : T.height uUpper = T.height zUpper := by
    by_cases hMarked : BucketMem p.marked sourceU.1.val (Frame.ref sourceU)
    · obtain ⟨hUMarked, hZMarked, hURow, hZRow, _⟩ :=
        build_common_parent_marker_rows p.reduced_build hMarkers hUP hZP hZUpper hOrder hOverlap
          hRootLe (.inl hMarked)
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
      exact hUpperB.trans ((congrArg (fun row => Row.B row (T.height parent)) hRows).trans hZUpperB.symm)
    · have hIff := build_common_parent_marker_iff p.reduced_build hMarkers hUP hZP
        hZUpper hOrder hOverlap hRootLe
      have hUUnmarked : sourceU.2.val ∉ (p.marked[sourceU.1.val]?.getD []).map Ref.index :=
        fun hm => hMarked ((root_source_marked_index_iff p sourceU).mp hm)
      have hZUnmarked : sourceZ.2.val ∉ (p.marked[sourceZ.1.val]?.getD []).map Ref.index :=
        fun hm => hMarked (hIff.mpr ((root_source_marked_index_iff p sourceZ).mp hm))
      obtain ⟨actualUUpper, actualZUpper, hURead, hZRead, hRows⟩ :=
        uCopy.common_parent_upper_rows_of_overlap zCopy hLast hUUnmarked hZUnmarked hUP hZP
          hZUpper hOrder hOverlap
      have hUCellEq : actualUUpper = upperUCell := Except.ok.inj (hURead.symm.trans hUpperURead)
      have hZCellEq : actualZUpper = upperZCell := Except.ok.inj (hZRead.symm.trans hUpperZRead)
      rw [hUCellEq, hZCellEq] at hRows
      exact (congrArg Cell.row hUUpperCell).trans (hRows.trans (congrArg Cell.row hZUpperCell).symm)
  refine ⟨{
    uCopy := uCopy, zCopy := zCopy, rootEndpoint := rootEndpoint
    u := u, z := z, parent := parent, uUpper := uUpper, zUpper := zUpper
    u_ref := hURef, z_ref := hZRef, parent_ref := hParentRef
    u_real := hUReal, z_real := hZReal, z_column := ?_
    u_parent := hUParent, z_parent := hZParent
    u_upper := hUUpper, z_upper := hZUpper', upper_height := hUpperRows }⟩
  have hUColumn := (congrArg Ref.column hURef).trans uCopy.source_column
  have hZColumn' := (congrArg Ref.column hZRef).trans zCopy.source_column
  change u.1.val = _ at hUColumn
  change z.1.val = _ at hZColumn'
  omega

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.recorded_root_common_parent_pair
