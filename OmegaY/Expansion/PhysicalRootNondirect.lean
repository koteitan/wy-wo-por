/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PhysicalRootNondirect.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PhysicalRootRecordGeometry
import OmegaY.Expansion.ActualAnyLastBlocker
import OmegaY.Expansion.HistoryRawInvariants

/-!
# Physical last-blocker recognition including a root-column source parent

The source candidate and blocker are strictly right of the root even when
their accepted common parent is in the root column. Their physical copies
give the actual new Q and its raw record path. Actual raw frontier geometry
identifies the two outgoing parent endpoints in the boundary column.
The only remaining numerical premise is the comparison of the actual
effective endpoints; the complete common fill addend is proved equal.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start ambient : Mountain} {references : List Ref}
  {source parent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references source parent ambient)

/-- This criterion includes a common source parent in the root column.
The supplied packet is source-derived; actual Q, the entire copied record
path, the common physical father and the fill-band comparison are proved
inside. Only strictly earlier copied columns are numerically recognized.
-/
theorem physical_comparison_criterion_all
    {next copies : Nat} (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (physical : PhysicalMarkerRead packet.pair.uCopy)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    (hBefore : source.1.val < next)
    (hLeft : ∀ (node father : (Frame.ofMountain ambient).Node),
      node.1.val < physical.outputRef.column → Real node →
      (Frame.ofMountain ambient).rawParent node = some father →
        (Frame.ofMountain ambient).P node = some father) :
    ∃ fatherRef, RawRefEdge ambient physical.outputRef fatherRef ∧
      ((Frame.ofMountain ambient).value packet.pair.u ≤ (Frame.ofMountain ambient).value packet.pair.z →
        Canonical.findParent ambient physical.outputRef = .ok fatherRef) := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered packet.source_parent).1.trans
      (Frame.P_value hNormal.toOrdered packet.source_parent).2)
  obtain ⟨actualParent, hActualParent, hParentBound, hSourceRow⟩ := p.real_marker_parent hReal hMarked
  have he : actualParent = parent := Option.some.inj (hActualParent.symm.trans packet.source_parent)
  subst actualParent
  have hZRight : p.root.column < packet.blocker.1.val :=
    hParentBound.trans_lt (Frame.P_column_lt hNormal.toOrdered packet.source_last_parent)
  have hQRight : p.root.column < packet.candidate.1.val :=
    hZRight.trans_le (packet.source_path.column_le hNormal.toOrdered)
  have hQBefore := (Frame.Q_column_lt hNormal.toOrdered packet.source_candidate).trans hBefore
  have hQMarked := (p.marked_candidate_of_right packet.source_parent packet.source_candidate hMarked hQRight).1
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  have hZMarked := (build_common_parent_marker_iff p.reduced_build hMarkers packet.source_parent
    packet.source_last_parent packet.source_z_upper packet.source_lower packet.source_overlap
    ((congrArg Ref.column hRootRef).trans_le hParentBound)).mp hMarked
  obtain ⟨candidateCopy⟩ := s.prior_effective_occurrence history hLast hQRight hQBefore
  obtain ⟨candidatePhysical⟩ := candidateCopy.physical_marker_read hQMarked
  obtain ⟨zCopy, hZEffectiveRef, hZEffectiveCell⟩ :
      ∃ zCopy : EffectiveCopyOccurrence p block start references packet.blocker ambient,
        Frame.ref packet.pair.z = zCopy.outputRef ∧ G.cell packet.pair.z = zCopy.read.outputCell := by
    rcases packet.pair.z_origin with ⟨hFixed, _⟩ | ⟨_, zCopy, hRef, hCell⟩
    · exact (not_lt_of_ge hFixed hZRight).elim
    · exact ⟨zCopy, hRef, hCell⟩
  obtain ⟨zPhysical⟩ := zCopy.physical_marker_read hZMarked
  have rawPath := s.recorded_physical_path history hLast packet.source_path hQMarked hZRight hQBefore
    candidatePhysical zPhysical
  obtain ⟨u, candidate, hURef, hCandidateRef, hQ, _⟩ :=
    physical.candidate_eq_of_candidate_right s.ambient_valid hMarked candidatePhysical
      packet.source_parent packet.source_candidate hQRight
  obtain ⟨z, hZRef, hZCell⟩ := Canonical.frame_node_of_cellAt zPhysical.output_read
  have hUCell : G.cell u = physical.cell := Except.ok.inj
    ((Canonical.cellAt_of_frame_node ambient u).symm.trans (by simpa only [hURef] using physical.output_read))
  have hUReal := physical.frame_real hReal hURef
  have hZRealSource := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered packet.source_last_parent).1.trans
      (Frame.P_value hNormal.toOrdered packet.source_last_parent).2)
  have hZReal := zPhysical.frame_real hZRealSource hZRef
  obtain ⟨uParentRef, hUEdge, hUParentColumn⟩ := physical.raw_parent_column_all hLast hMarked packet.source_parent
  obtain ⟨zParentRef, hZEdge, hZParentColumn⟩ := zPhysical.raw_parent_column_all hLast hZMarked packet.source_last_parent
  have hUEdgeRead := hUEdge
  have hZEdgeRead := hZEdge
  obtain ⟨_, _, _, _, _, _, hUParentRead⟩ := hUEdgeRead
  obtain ⟨_, _, _, _, _, _, hZParentRead⟩ := hZEdgeRead
  obtain ⟨uParent, hUParentRef, _⟩ := Canonical.frame_node_of_cellAt hUParentRead
  obtain ⟨zParent, hZParentRef, _⟩ := Canonical.frame_node_of_cellAt hZParentRead
  have hRawU := hUEdge.rawParent hURef hUParentRef
  have hRawZ := hZEdge.rawParent hZRef hZParentRef
  have hZSourceRow := (build_marked_parent_bounds p.reduced_build hMarkers packet.source_last_parent hZMarked).2
  have hRows : G.height u = G.height z := by
    change (G.cell u).row = (G.cell z).row
    rw [hUCell, hZCell, physical.source_row, zPhysical.source_row]
    exact hSourceRow.trans hZSourceRow.symm
  have hParentColumns : uParent.1 = zParent.1 := Fin.ext
    (((congrArg Ref.column hUParentRef).trans hUParentColumn).trans
      ((congrArg Ref.column hZParentRef).trans hZParentColumn).symm)
  obtain ⟨hRawGeometry, hFatherBound⟩ := s.raw_invariants_of_start_run history hLast hStartRun
  have hParents := Frame.rawParent_eq_of_child_height_parent_column s.ambient_valid.toOrdered
    hRawGeometry hFatherBound hUReal hZReal hRawU hRawZ hRows hParentColumns
  have hRawZ' : G.rawParent z = some uParent := by simpa only [hParents] using hRawZ
  have hUColumn : u.1.val = physical.outputRef.column := congrArg Ref.column hURef
  have hLeftAtU : ∀ (node father : G.Node), node.1.val < u.1.val → Real node →
      G.rawParent node = some father → G.P node = some father := by
    intro node father hColumn hNodeReal hRaw
    exact hLeft node father (hColumn.trans_eq hUColumn) hNodeReal hRaw
  have path := rawPath.toParentPath_of_recognition s.ambient_valid.toOrdered hLeftAtU
    hCandidateRef hZRef (Frame.Q_real s.ambient_valid.toOrdered hUReal hQ)
    (Frame.Q_column_lt s.ambient_valid.toOrdered hQ)
  have hZP := hLeftAtU z uParent
    ((path.column_le s.ambient_valid.toOrdered).trans_lt (Frame.Q_column_lt s.ambient_valid.toOrdered hQ))
    hZReal hRawZ'
  have hSums := s.mountainSums_of_start_run history hLast hStartRun
  obtain ⟨upper, hUpper, _⟩ := Frame.rawParent_spec hRawU
  obtain ⟨actual, hActual, _, _, hSmall, _⟩ := hSums.rawParent_upper s.ambient_valid hUReal hUpper
  have he : actual = uParent := Option.some.inj (hActual.symm.trans hRawU)
  subst actual
  refine ⟨uParentRef, hUEdge, ?_⟩
  intro hBarrier
  have hEffective : packet.pair.uCopy.read.outputCell.value ≤ zCopy.read.outputCell.value := by
    change (G.cell packet.pair.u).value ≤ (G.cell packet.pair.z).value at hBarrier
    rw [packet.pair.u_cell, hZEffectiveCell] at hBarrier
    exact hBarrier
  have hPhysical := ((physical.compare_effective_all zPhysical hLast s.ambient_valid hSums
    packet.source_parent packet.source_last_parent hMarked hZMarked hParentBound).1).mpr hEffective
  have hValues : G.value u ≤ G.value z := by
    change (G.cell u).value ≤ (G.cell z).value
    rw [hUCell, hZCell]
    exact hPhysical
  have hP := Frame.P_of_record_barrier s.ambient_valid.toOrdered hQ path hZP hValues hSmall
  simpa only [hURef, hUParentRef] using (Executable.findParent_ref_iff s.ambient_valid.toOrdered u uParent).mpr hP

end AnySourceBlockerPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.AnySourceBlockerPacket.physical_comparison_criterion_all
