/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkedEffectiveSearch.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualStationaryEffectiveCandidate
import OmegaY.Expansion.PreservedSearchNodes

/-!
# Search at an actually raised marker's effective endpoint

The effective target is the last fill rung, not the physical marker. Its
first candidate and numerical parent are the source P parent's effective
occurrence. They need not be the source Q candidate's effective occurrence.
The physical-to-effective vertical band is not a numerical-parent path.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem ref_eq_of_same_column_row {mountain : Mountain}
    (hValid : MountainValid mountain) {left right : Ref} {a b : Cell}
    (hA : Canonical.cellAt mountain left = .ok a)
    (hB : Canonical.cellAt mountain right = .ok b)
    (hColumn : left.column = right.column) (hRow : a.row = b.row) : left = right := by
  obtain ⟨nodes, hNodes, hLeft⟩ := cellAt_ok_iff.mp hA
  obtain ⟨others, hOthers, hRight⟩ := cellAt_ok_iff.mp hB
  have he : others = nodes := Option.some.inj (hOthers.symm.trans (hColumn ▸ hNodes))
  subst others
  obtain ⟨hc, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hCV : ColumnValid mountain left.column nodes := hNodesEq ▸ hValid _ hc
  have hIndex := column_read_index_eq_of_row hCV hLeft hRight hRow
  cases left
  cases right
  simp only [Ref.mk.injEq]
  exact ⟨hColumn, hIndex⟩

/-- The last actual fill rung's first candidate is exactly its upper
parent endpoint. This uses the executed sorted splice, not a numerical P
or copied Normal premise. -/
theorem ColumnCopyData.raised_marker_target_candidate
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hUpper : (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0)
    (hRoot : rootColumn ≤ (d.marker_data marker hm).sourceParent.column)
    (hRaised : (d.marker_data marker hm).current.row < (d.marker_data marker hm).targetCell.row)
    {index : Nat} {current : Cell} (hRead : column[index]? = some current)
    (hRow : current.row = (d.marker_data marker hm).targetCell.row) :
    nextCandidate (mountain.push column) ⟨mountain.size, index⟩ =
      .ok ⟨(d.marker_data marker hm).sourceParent.column + shift, (d.marker_data marker hm).targetIndex⟩ := by
  let md := d.marker_data marker hm
  obtain ⟨actual, hActual, _, hValid, _, hMountainValid⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  obtain ⟨parentIndex, parent, before, after, hNext, hParent, hSplit⟩ :=
    d.fill_contour_splice hParentPower hParentLow hNoPremature hm hUpper hRoot hRaised
  obtain ⟨lower, upper, hLower, _, hLowerShape, _⟩ := finish_adjacent_of_splice
    (d.copyColumn_eq_finish.symm.trans hRun) hSplit (index := 0) rfl rfl
  simp only [Nat.add_zero] at hLower
  have hLowerRow : lower.row = md.targetCell.row := hLowerShape.1.symm
  have hIndex := column_read_index_eq_of_row hValid hLower hRead (hLowerRow.trans hRow.symm)
  have hCellEq : lower = current := Option.some.inj (hLower.symm.trans (hIndex ▸ hRead))
  have hLeft : current.left = some ⟨md.sourceParent.column + shift, parentIndex⟩ :=
    hCellEq ▸ hLowerShape.2.symm
  have hParentColumn := (Array.getElem?_eq_some_iff.mp md.parent_nodes).1
  have hParentRead : Canonical.cellAt (mountain.push column)
      ⟨md.sourceParent.column + shift, parentIndex⟩ = .ok parent := by
    rw [Canonical.cellAt_push_left hParentColumn]
    exact cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, hParent⟩
  have hTargetRead : Canonical.cellAt (mountain.push column)
      ⟨md.sourceParent.column + shift, parentIndex + 1⟩ = .ok md.targetCell := by
    rw [Canonical.cellAt_push_left hParentColumn]
    exact cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, by simpa only [hNext] using md.target_at⟩
  obtain ⟨u, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt
    (show Canonical.cellAt (mountain.push column) ⟨mountain.size, index⟩ = .ok current from
      cellAt_ok_iff.mpr ⟨column, by simp, hRead⟩)
  obtain ⟨left, hLeftRef, _⟩ := Canonical.frame_node_of_cellAt hParentRead
  obtain ⟨target, hTargetRef, hTargetCell⟩ := Canonical.frame_node_of_cellAt hTargetRead
  have hTargetUpper := Frame.upper_of_refs hLeftRef hTargetRef
  have hCandidate := Frame.Q_eq_upper_at_equal hMountainValid.toOrdered
    (show ((Frame.ofMountain (mountain.push column)).cell u).left = some (Frame.ref left) by
      rw [hUCell, hLeftRef]; exact hLeft) hTargetUpper
    (show (Frame.ofMountain (mountain.push column)).height target =
        (Frame.ofMountain (mountain.push column)).height u by
      simpa only [Frame.height, hUCell, hTargetCell] using hRow.symm)
  have hSearch := (Executable.nextCandidate_ref_iff hMountainValid.toOrdered u target).mpr hCandidate
  simpa only [hURef, hTargetRef, hNext] using hSearch

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- A genuinely raised marker bypasses any rejected old Q records at its
effective target. The actual last-fill seam supplies both searches directly.
No comparison between copied source values is assumed. -/
theorem raised_marker_search (hLast : 1 < last) (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent : (Frame.ofMountain p.reduced).Node}
    (parentCopy : EffectiveCopyOccurrence p block start references parent result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hRight : p.root.column < parent.1.val)
    (hRaised : (Frame.ofMountain p.reduced).height source < copy.read.outputCell.row) :
    nextCandidate result copy.outputRef = .ok parentCopy.outputRef ∧
      findParent result copy.outputRef = .ok parentCopy.outputRef := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  let md := d.marker_data copy.read.marker copy.read.marker_mem
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hSources : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hMarkerIndex := copy.read.marker_index_of_marked hMarked
  have hCurrent : md.current = F.cell source := Option.some.inj
    (md.current_at.symm.trans (by simpa only [hMarkerIndex] using copy.read.source_at))
  have hOutputTarget : copy.read.outputCell.row = md.targetCell.row := by
    rw [copy.read.output_row]
    change Row.lift md.current.row md.targetCell.row (F.height source) = _
    rw [hCurrent]
    exact Row.lift_at_root _ _
  have hMarkerRaised : md.current.row < md.targetCell.row := by
    rw [hCurrent, ← hOutputTarget]
    exact hRaised
  obtain ⟨sourceUpper, hSourceUpper⟩ := hNormal.upper_of_parent hParent
  have hUpperAt : d.sources[source.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSources (congrArg Fin.val (Frame.upper_spec hSourceUpper).1)
    simpa only [(Frame.upper_spec hSourceUpper).2] using hRead
  have hUpperCell : md.upper = F.cell sourceUpper := Option.some.inj
    (md.upper_at.symm.trans (by simpa only [hMarkerIndex] using hUpperAt))
  obtain ⟨actualParent, hActualParent, _, _, hStored⟩ := hNormal.upper_step source sourceUpper hReal hSourceUpper
  have he : actualParent = parent := Option.some.inj (hActualParent.symm.trans hParent)
  subst actualParent
  have hSourceParent : md.sourceParent = Frame.ref parent := Option.some.inj
    (md.upper_left.symm.trans (by simpa only [hUpperCell] using hStored))
  obtain ⟨hNoPremature, hParentPower, hParentLow⟩ :=
    copy.state.column_data_parent_inputs hLast source.1.isLt d
  obtain ⟨step, hLowerRow, _⟩ := d.prepared_fill_contour_seam hSources
    hParentPower hParentLow hNoPremature copy.read.copy_run copy.read.marker_mem hMarkerRaised
  obtain ⟨actual, hActual, _, hColumnValid, _, _⟩ := d.copyColumn_valid
  have he : actual = copy.column := Except.ok.inj (hActual.symm.trans copy.read.copy_run)
  subst actual
  have hStepIndex := column_read_index_eq_of_row hColumnValid step.lower_at copy.read.output_at
    (hLowerRow.trans hOutputTarget.symm)
  have hLocalP : findParent (copy.before.push copy.column) copy.outputRef =
      .ok ⟨md.sourceParent.column + block * (p.reduced.size - 1 - p.root.column), md.targetIndex⟩ := by
    simpa only [outputRef, EffectiveCopyRead.outputRef, hStepIndex] using step.parent_found
  obtain ⟨hMarkerUpper, hMarkerRoot⟩ := d.prepared_marker_successor hSources copy.read.marker_mem hMarkerRaised
  have hLocalQ := d.raised_marker_target_candidate hParentPower hParentLow hNoPremature
    copy.read.copy_run copy.read.marker_mem hMarkerUpper hMarkerRoot hMarkerRaised copy.read.output_at hOutputTarget
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨hParentMarked, hSourceRow⟩ := build_marked_parent p.reduced_build hMarkers hParent hMarked
    ((congrArg Ref.column hRootRef).trans_lt hRight)
  have hParentReference : referenceAt start references (F.height parent) = .ok parentCopy.read.outputCell.row :=
    (parentCopy.state.referenceAt_preserved _).symm.trans (parentCopy.read.marked_reference hParentMarked)
  have hTargetReference : referenceAt start references (F.height parent) = .ok md.targetCell.row := by
    have h := (copy.state.referenceAt_preserved md.current.row).symm.trans md.reference
    have hRow : md.current.row = F.height parent := (congrArg Cell.row hCurrent).trans hSourceRow
    simpa only [hRow] using h
  have hTargetRow : md.targetCell.row = parentCopy.read.outputCell.row :=
    Except.ok.inj (hTargetReference.symm.trans hParentReference)
  let targetRef : Ref := ⟨md.sourceParent.column + block * (p.reduced.size - 1 - p.root.column), md.targetIndex⟩
  have hTargetRead : Canonical.cellAt copy.before targetRef = .ok md.targetCell :=
    cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, md.target_at⟩
  have hOldBound : targetRef.column < copy.before.size := (Array.getElem?_eq_some_iff.mp md.parent_nodes).1
  have hPreserve : PreservesColumns copy.before result :=
    (PreservesColumns.push copy.before copy.column).trans copy.preserved
  have hTargetResult : Canonical.cellAt result targetRef = .ok md.targetCell :=
    (hPreserve.cellAt hOldBound).trans hTargetRead
  have hTargetRef : targetRef = parentCopy.outputRef := ref_eq_of_same_column_row hValid
    hTargetResult parentCopy.output_read
    (by change md.sourceParent.column + _ = _; rw [hSourceParent, parentCopy.source_column]; rfl) hTargetRow
  have hCopyBound : copy.outputRef.column < (copy.before.push copy.column).size := by
    simp [outputRef, EffectiveCopyRead.outputRef]
  constructor
  · rw [copy.preserved.nextCandidate hCopyBound]
    exact hLocalQ.trans (congrArg Except.ok hTargetRef)
  · rw [copy.preserved.findParent hCopyBound]
    simpa only [← hTargetRef] using hLocalP

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.raised_marker_target_candidate
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.raised_marker_search
