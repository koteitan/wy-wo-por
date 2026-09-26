/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualStationaryMarkerCandidate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMarkedEffectiveSearch

/-!
# Actual first candidates of stationary markers

The physical marker is recovered from its executed segment. The source
candidate is proved marked at the same row, so it shares the stationary
reference target. No copied value comparison or numerical parent is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- The old first candidate of an actual real weak marker with a strict-right
parent is itself a marker at the same source row. -/
theorem build_marked_candidate {input : List Nat} {mountain : Mountain}
    (hBuild : build input = .ok mountain)
    {root source candidate parent : (Frame.ofMountain mountain).Node}
    {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref root) = .ok marked)
    (hParent : (Frame.ofMountain mountain).P source = some parent)
    (hCandidate : (Frame.ofMountain mountain).Q source = some candidate)
    (hMarked : BucketMem marked source.1.val (Frame.ref source))
    (hRight : root.1.val < parent.1.val) :
    BucketMem marked candidate.1.val (Frame.ref candidate) ∧
      (Frame.ofMountain mountain).height candidate = (Frame.ofMountain mountain).height source := by
  let F := Frame.ofMountain mountain
  have hNormal := build_normal_of_success hBuild
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hCandidateReal := Frame.Q_real hNormal.toOrdered hReal hCandidate
  obtain ⟨hParentMarked, hRows⟩ := build_marked_parent hBuild hMarkers hParent hMarked hRight
  have hParentReal := Frame.real_of_value_pos hNormal.toOrdered (Frame.P_value hNormal.toOrdered hParent).1
  obtain ⟨_, low, hLowReal, hLowColumn, hLowIndex, hParentPath, hParentRow⟩ :=
    (build_markers_real_member_iff_parentPath hBuild hMarkers hParentReal).mp hParentMarked
  obtain ⟨actual, hActual, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
  have he : actual = candidate := Option.some.inj (hActual.symm.trans hCandidate)
  subst actual
  have hPath := trace.parentPath hNormal.toOrdered (hNormal.real_positive candidate hCandidateReal)
  have hSame : F.height candidate = F.height source := le_antisymm
    (Frame.Q_height_le hNormal.toOrdered hCandidate)
    (hRows ▸ hPath.height_le hNormal.toOrdered)
  exact ⟨(build_markers_real_member_iff_parentPath hBuild hMarkers hCandidateReal).mpr
    ⟨hRight.trans_le (hPath.column_le hNormal.toOrdered), low, hLowReal,
      hLowColumn, hLowIndex, hPath.trans hParentPath, hSame.trans (hRows.trans hParentRow)⟩, hSame⟩

/-- A stationary marker's effective occurrence is the actual physical copy
from its own executed segment, including its actual stored left leg. -/
theorem EffectiveCopyRead.stationary_marker_copy_execution
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn sourceIndex : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {sourceCell : Cell} {column : Column}
    (read : EffectiveCopyRead d sourceIndex sourceCell column)
    (hMarked : (⟨sourceColumn, sourceIndex⟩ : Ref) ∈ d.bucket)
    (hStationary : read.outputCell.row = sourceCell.row) :
    ∃ copied, copyEdge mountain ⟨sourceColumn, sourceIndex⟩ shift rootColumn
      read.outputCell.row = .ok copied ∧ SameShape copied read.outputCell := by
  let md := d.marker_data read.marker read.marker_mem
  have hIndex := read.marker_index_of_marked hMarked
  have hCurrent : md.current = sourceCell := Option.some.inj
    (md.current_at.symm.trans (by simpa only [hIndex] using read.source_at))
  obtain ⟨copied, path, gap, hResult, hCopy, _, _, _, _, _, _, _⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero
      d.destination.le d.source_top references (d.bucket.map Ref.index) md.current_at
      md.upper_at md.upper_left md.parent_nodes md.target_at md.reference md.target_lower
      (d.segment_run read.marker_mem)
  have hCandidate : copied ∈ d.candidates := List.mem_flatMap.mpr
    ⟨read.marker, read.marker_mem, by simp [hResult]⟩
  obtain ⟨index, output, hOutput, hShape⟩ := finish_candidate_read
    (d.copyColumn_eq_finish.symm.trans read.copy_run) hCandidate
  have hSameRow : output.row = read.outputCell.row :=
    hShape.1.symm.trans ((copyEdge_return_row hCopy).trans ((congrArg Cell.row hCurrent).trans hStationary.symm))
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans read.copy_run)
  subst actual
  have hOutputIndex := column_read_index_eq_of_row hValid hOutput read.output_at hSameRow
  have hOutputEq : output = read.outputCell :=
    Option.some.inj (hOutput.symm.trans (hOutputIndex ▸ read.output_at))
  refine ⟨copied, ?_, hOutputEq ▸ hShape⟩
  simpa only [hIndex, hCurrent, hStationary] using hCopy

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- An executed own-cell copy identifies the new Q as the inclusive frontier
of the source Q column. This interface does not presume a copied candidate. -/
theorem candidate_frontier_of_copy_execution (hValid : MountainValid result)
    (hReal : Frame.Real source) {copied : Cell}
    (hCopy : copyEdge copy.before (Frame.ref source) (block * (p.reduced.size - 1 - p.root.column))
      p.root.column copy.read.outputCell.row = .ok copied)
    (hShape : SameShape copied copy.read.outputCell)
    {candidate : (Frame.ofMountain p.reduced).Node}
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hMoved : p.root.column ≤ candidate.1.val) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      (Frame.ofMountain result).cell actualSource = copy.read.outputCell ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok (Frame.ref actualCandidate) ∧
      actualCandidate.1.val = candidate.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      ∃ hCut : (1 : Row) ≤ copy.read.outputCell.row,
        Frame.frontierAt hValid.toOrdered copy.read.outputCell.row hCut actualCandidate.1 =
          actualCandidate := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceRead : lookup copy.before (Frame.ref source) = .ok (F.cell source) :=
    lookup_ok_iff.mpr ⟨copy.data.sources, copy.data.source_column, copy.read.source_at⟩
  have hPositive : (0 : Row) < (F.cell source).row :=
    Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hReal)
  obtain ⟨expected, parentRef, parentCell, hExpected, _, _, hExpectedLeft,
      hParentRead, hParentColumn, oldParent, hOldLeft, _, hEndpoint⟩ :=
    copyEdge_nonphantom_total copy.data.ambient_valid hSourceRead copy.data.source_nonzero
      copy.data.destination.le (ne_of_gt hPositive)
      (hPositive.trans_le copy.read.source_row_le_output)
  have hExpectedEq : expected = copied := Except.ok.inj (hExpected.symm.trans hCopy)
  subst expected
  obtain ⟨oldLeft, hLeft, _, _, hCandidateColumn, _⟩ :=
    Frame.Q_spec hNormal.toOrdered hCandidate
  have hOldParent : oldParent = Frame.ref oldLeft :=
    Option.some.inj (hOldLeft.symm.trans hLeft)
  have hOldColumn : oldParent.column = candidate.1.val := by
    rw [hOldParent]
    exact (congrArg Fin.val hCandidateColumn).symm
  have hSelectedColumn : parentRef.column =
      candidate.1.val + block * (p.reduced.size - 1 - p.root.column) := by
    rcases hEndpoint with ⟨hFixed, _, _⟩ | ⟨_, hColumn, _, _⟩
    · rw [hOldColumn] at hFixed
      exact False.elim (not_lt_of_ge hMoved hFixed)
    · exact hColumn.trans (congrArg (fun n => n + block *
        (p.reduced.size - 1 - p.root.column)) hOldColumn)
  have hParentBound : parentRef.column < copy.before.size :=
    copy.data.destination ▸ hParentColumn
  have hParentResult : Canonical.cellAt result parentRef = .ok parentCell :=
    (copy.preserved.cellAt (by simpa using Nat.lt_succ_of_lt hParentBound)).trans
      (((PreservesColumns.push copy.before copy.column).cellAt hParentBound).trans
      (cellAt_ok_iff.mpr (lookup_ok_iff.mp hParentRead)))
  obtain ⟨actualParent, hActualParentRef, _⟩ := Canonical.frame_node_of_cellAt hParentResult
  obtain ⟨actualSource, hActualSourceRef, hActualSourceCell⟩ :=
    Canonical.frame_node_of_cellAt copy.output_read
  have hActualLeft : (G.cell actualSource).left = some (Frame.ref actualParent) := by
    rw [hActualSourceCell, hActualParentRef]
    exact hShape.2.symm.trans hExpectedLeft
  obtain ⟨actualCandidate, hActualCandidate, hSearch⟩ :=
    Executable.candidate_of_stored hValid.toOrdered hActualLeft
  obtain ⟨selected, hSelected, _, _, hActualColumn, _⟩ :=
    Frame.Q_spec hValid.toOrdered hActualCandidate
  have hSelectedEq : selected = actualParent := Executable.ref_injective G
    (Option.some.inj (hSelected.symm.trans hActualLeft))
  subst selected
  have hActualReal : Frame.Real actualSource := by
    have hIndex := congrArg Ref.index hActualSourceRef
    change actualSource.2.val = copy.read.outputIndex at hIndex
    change 0 < actualSource.2.val
    rw [hIndex]
    exact copy.read.output_real hReal
  have hCut : (1 : Row) ≤ copy.read.outputCell.row := by
    rw [← hActualSourceCell]
    exact Frame.one_le_height hValid.toOrdered hActualReal
  refine ⟨actualSource, actualCandidate, hActualSourceRef, hActualSourceCell,
    hActualCandidate, ?_, ?_, hCut, ?_⟩
  · simpa only [hActualSourceRef] using hSearch
  · exact (congrArg Fin.val hActualColumn).trans
      ((congrArg Ref.column hActualParentRef).trans hSelectedColumn)
  · apply Frame.frontierAt_eq_of_upper_barrier hValid.toOrdered hCut
    · simpa only [Frame.height, hActualSourceCell] using
        Frame.Q_height_le hValid.toOrdered hActualCandidate
    · intro upper hUpper
      simpa only [Frame.height, hActualSourceCell] using
        Frame.Q_upper_gt hValid.toOrdered hActualCandidate hUpper

/-- At a stationary physical/effective marker the actual first candidate is
the old first candidate's effective occurrence. No numerical P on the output
or copied value comparison is used. -/
theorem candidate_eq_stationary_marker (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentRight : p.root.column < parent.1.val)
    (hStationary : copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      Frame.ref actualCandidate = candidateCopy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok candidateCopy.outputRef := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨hCandidateMarked, hSourceRows⟩ := build_marked_candidate p.reduced_build
    hMarkers hParent hCandidate hMarked ((congrArg Ref.column hRootRef).trans_lt hParentRight)
  have hSourceReference : referenceAt start references (F.height source) = .ok copy.read.outputCell.row :=
    (copy.state.referenceAt_preserved _).symm.trans (copy.read.marked_reference hMarked)
  have hCandidateReference : referenceAt start references (F.height source) = .ok candidateCopy.read.outputCell.row := by
    have h := (candidateCopy.state.referenceAt_preserved _).symm.trans
      (candidateCopy.read.marked_reference hCandidateMarked)
    change referenceAt start references (F.height candidate) = .ok candidateCopy.read.outputCell.row at h
    have hRows : F.height candidate = F.height source := hSourceRows
    rw [hRows] at h
    exact h
  have hOutputRows : candidateCopy.read.outputCell.row = copy.read.outputCell.row :=
    Except.ok.inj (hCandidateReference.symm.trans hSourceReference)
  obtain ⟨copied, hCopy, hShape⟩ := copy.read.stationary_marker_copy_execution hMarked hStationary
  obtain ⟨actual, hActual, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
  have he : actual = candidate := Option.some.inj (hActual.symm.trans hCandidate)
  subst actual
  have hCandidateReal := Frame.Q_real hNormal.toOrdered hReal hCandidate
  have hPath := trace.parentPath hNormal.toOrdered (hNormal.real_positive candidate hCandidateReal)
  have hMoved := hParentRight.trans_le (hPath.column_le hNormal.toOrdered)
  obtain ⟨actualSource, actualCandidate, hSourceRef, _, hActualQ, hSearch,
      hColumn, hCut, hFront⟩ :=
    copy.candidate_frontier_of_copy_execution hValid hReal hCopy hShape hCandidate hMoved.le
  obtain ⟨expected, hExpectedRef, hExpectedCell⟩ :=
    Canonical.frame_node_of_cellAt candidateCopy.output_read
  have hExpectedRow : G.height expected = copy.read.outputCell.row := by
    change (G.cell expected).row = _
    rw [hExpectedCell, hOutputRows]
  have hColumns : expected.1 = actualCandidate.1 := Fin.ext
    ((congrArg Ref.column hExpectedRef).trans candidateCopy.source_column |>.trans hColumn.symm)
  have hExpectedFront : Frame.frontierAt hValid.toOrdered copy.read.outputCell.row hCut expected.1 =
      expected := by
    apply Frame.frontierAt_eq_of_upper_barrier hValid.toOrdered hCut
    · exact hExpectedRow.le
    · intro upper hUpper
      rw [← hExpectedRow]
      have hSpec := Frame.upper_spec hUpper
      rcases upper with ⟨column, index⟩
      dsimp only at hSpec
      obtain ⟨hColumnEq, hIndex⟩ := hSpec
      subst column
      exact hValid.toOrdered.rows_strict expected.1 (by change expected.2.val < index.val; omega)
  rw [hColumns, hFront] at hExpectedFront
  have hActualRef : Frame.ref actualCandidate = candidateCopy.outputRef :=
    (congrArg Frame.ref hExpectedFront).trans hExpectedRef
  exact ⟨actualSource, actualCandidate, hSourceRef, hActualRef, hActualQ,
    by simpa only [hActualRef] using hSearch⟩

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_marked_candidate
#print axioms OmegaY.Expansion.EffectiveCopyRead.stationary_marker_copy_execution
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_frontier_of_copy_execution
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_stationary_marker
