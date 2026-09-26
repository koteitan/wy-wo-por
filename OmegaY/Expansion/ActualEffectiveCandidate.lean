/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveCandidate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRaisedSeamParent
import OmegaY.Expansion.RawFrontier
import OmegaY.Geometry.PathBranch

/-!
# The actual search start of a copied nonmarker

The source cell itself is recovered from the executed contour, including its
first cell above a marker. Consequently its copied stored leg identifies the
source candidate's translated column. The actual new Q is that column's
inclusive frontier at the effective child row. This does not presume that
the frontier is the effective occurrence of the old candidate.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem source_contour_index {nodes : Column} {markers : List Nat}
    {index position : Nat} {current cell : Cell}
    (hRead : (contourSourceCells markers index current
      (nodes.toList.drop (index + 1)))[position]? = some cell) :
    nodes[index + position + 1]? = some cell := by
  rw [contourSourceCells_eq_take, List.getElem?_take] at hRead
  split at hRead
  · simpa only [List.getElem?_drop, Array.getElem?_toList,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hRead
  · cases hRead

/-- This is the actual copy call for the nonmarker itself, not only the
copy call for its successor. Its occurrence is identified after finishing. -/
theorem EffectiveCopyRead.nonmarker_copy_execution
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn sourceIndex : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {sourceCell : Cell} {column : Column}
    (read : EffectiveCopyRead d sourceIndex sourceCell column)
    (hNoPremature : NoPrematureOne d.sources)
    (hUnmarked : sourceIndex ∉ d.bucket.map Ref.index) :
    ∃ copied, copyEdge mountain ⟨sourceColumn, sourceIndex⟩ shift rootColumn
      read.outputCell.row = .ok copied ∧ SameShape copied read.outputCell := by
  let md := d.marker_data read.marker read.marker_mem
  have hAfter : read.marker.index < sourceIndex := by
    have hMarked : read.marker.index ∈ d.bucket.map Ref.index :=
      List.mem_map.mpr ⟨read.marker, read.marker_mem, rfl⟩
    have hBefore := read.marker_before
    apply lt_of_le_of_ne hBefore
    intro hEq
    exact hUnmarked (hEq ▸ hMarked)
  have hMember := mem_contourSourceCells_of_no_between hNoPremature
    (d.bucket.map Ref.index) md.current_at read.source_at hAfter read.no_between rfl
  obtain ⟨position, hPosition⟩ := List.mem_iff_getElem?.mp hMember
  have hIndex : read.marker.index + position + 1 = sourceIndex :=
    column_read_index_eq_of_row d.source_valid (source_contour_index hPosition) read.source_at rfl
  obtain ⟨markerCopy, path, gap, hResult, _, _, _, hContour, _, _, _, _⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
      d.source_top references (d.bucket.map Ref.index) md.current_at md.upper_at md.upper_left
      md.parent_nodes md.target_at md.reference md.target_lower (d.segment_run read.marker_mem)
  have hRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column d.source_nonzero
    d.destination.le d.source_top d.source_power (d.bucket.map Ref.index)
    md.targetCell.row md.current_at rfl hContour
  have hRowRead : (path.map Cell.row)[position]? =
      some (Row.lift md.current.row md.targetCell.row sourceCell.row) := by
    rw [hRows]
    simp only [List.getElem?_map, hPosition, Option.map_some]
  obtain ⟨copied, hCopied, hCopiedRow⟩ := cell_read_of_row_read hRowRead
  have hContourLift : contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn
      read.marker.index (Row.lift md.current.row md.targetCell.row md.current.row)
      md.current (d.sources.toList.drop (read.marker.index + 1)) = .ok path := by
    simpa only [Row.lift_at_root] using hContour
  obtain ⟨execution⟩ := contour_execution_at d.source_power (d.bucket.map Ref.index)
    md.current_at le_rfl rfl hContourLift hCopied
  have hUpper : execution.upper = sourceCell := Option.some.inj
    (execution.upper_at.symm.trans (by simpa only [hIndex] using read.source_at))
  have hCandidate : copied ∈ d.candidates := List.mem_flatMap.mpr
    ⟨read.marker, read.marker_mem, by
      rw [hResult]
      simp only [List.mem_append, List.mem_cons]
      exact Or.inl (Or.inr (List.mem_of_getElem? hCopied))⟩
  obtain ⟨index, output, hOutput, hShape⟩ :=
    finish_candidate_read (d.copyColumn_eq_finish.symm.trans read.copy_run) hCandidate
  have hSameRow : output.row = read.outputCell.row := by
    rw [read.output_row]
    exact hShape.1.symm.trans hCopiedRow
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have hActualEq : actual = column := Except.ok.inj (hActual.symm.trans read.copy_run)
  subst actual
  have hOutputIndex := column_read_index_eq_of_row hValid hOutput read.output_at hSameRow
  have hOutputEq : output = read.outputCell :=
    Option.some.inj (hOutput.symm.trans (hOutputIndex ▸ read.output_at))
  refine ⟨copied, ?_, hOutputEq ▸ hShape⟩
  simpa only [hIndex, hUpper, read.output_row] using execution.copy_run

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- The actual new Q, including its executable search, is identified as
the inclusive frontier of the translated source-candidate column. The
frontier may not yet be identified with the old candidate's effective copy. -/
theorem candidate_frontier (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
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
  have hReal : Frame.Real source := by
    change 0 < source.2.val
    by_contra hNot
    have hZero : source.2.val = 0 := by omega
    apply hUnmarked
    exact List.mem_map.mpr ⟨⟨source.1.val, 0⟩, copy.data.phantom_marker, hZero.symm⟩
  have hNoPremature := (copy.state.column_data_parent_inputs hLast source.1.isLt copy.data).1
  obtain ⟨copied, hCopy, hShape⟩ := copy.read.nonmarker_copy_execution hNoPremature hUnmarked
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

private theorem candidate_height_max {F : Frame} (hF : F.Ordered)
    {source candidate other : F.Node} (hReal : Frame.Real source)
    (hCandidate : F.Q source = some candidate) (hColumn : other.1 = candidate.1)
    (hBelow : F.height other ≤ F.height source) : F.height other ≤ F.height candidate := by
  have hCut := Frame.one_le_height hF hReal
  have hFront := Frame.frontierAt_eq_of_upper_barrier hF hCut
    (Frame.Q_height_le hF hCandidate) (fun _ h => Frame.Q_upper_gt hF hCandidate h)
  have hMaximum := (Frame.frontierAt_spec hF hCut candidate.1).2.2.2.1
  have hFrontIndex := congrArg (fun node : F.Node => node.2.val) hFront
  rcases other with ⟨column, index⟩
  dsimp only at hColumn
  subst column
  have hBound : index.val ≤ candidate.2.val := by
    have h := hMaximum index hBelow
    change index.val ≤ (Frame.frontierAt hF (F.height source) hCut candidate.1).2.val at h
    simpa only [hFrontIndex] using h
  exact (hF.rows_strict candidate.1).monotone hBound

/-- In the unchanged high tail there can be no extra fill/marker candidate:
every output row above the effective old candidate has an actual source row.
This identifies the real new search start, not only its column or its value. -/
theorem candidate_eq_high (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hMoved : p.root.column ≤ candidate.1.val)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height candidate) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      Frame.ref actualCandidate = candidateCopy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok candidateCopy.outputRef := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hCandidateBelow := Frame.Q_height_le hNormal.toOrdered hCandidate
  have hSourceHigh := hHigh.trans hCandidateBelow
  have hSourceRow := copy.high_row hLast hSourceHigh
  have hCandidateRow := candidateCopy.high_row hLast hHigh
  obtain ⟨actualSource, actualCandidate, hSourceRef, hSourceCell, hActualQ, hSearch,
      hColumn, hCut, hFront⟩ := copy.candidate_frontier hLast hValid hUnmarked hCandidate hMoved
  obtain ⟨expected, hExpectedRef, hExpectedCell⟩ :=
    Canonical.frame_node_of_cellAt candidateCopy.output_read
  have hExpectedRow : G.height expected = F.height candidate := by
    change (G.cell expected).row = _
    rw [hExpectedCell, hCandidateRow]
  have hColumns : expected.1 = actualCandidate.1 := Fin.ext
    ((congrArg Ref.column hExpectedRef).trans candidateCopy.source_column |>.trans hColumn.symm)
  have hExpectedFront : Frame.frontierAt hValid.toOrdered copy.read.outputCell.row hCut expected.1 =
      expected := by
    apply Frame.frontierAt_eq_of_upper_barrier hValid.toOrdered hCut
    · rw [hSourceRow, hExpectedRow]
      exact hCandidateBelow
    · intro upper hUpper
      have hUpperSpec := Frame.upper_spec hUpper
      have hHigher : G.height expected < G.height upper := by
        rcases upper with ⟨column, index⟩
        dsimp only at hUpperSpec
        obtain ⟨hColumnEq, hIndex⟩ := hUpperSpec
        subst column
        exact hValid.toOrdered.rows_strict expected.1 (by change expected.2.val < index.val; omega)
      have hUpperColumn : upper.1.val = candidateCopy.before.size :=
        (congrArg Fin.val hUpperSpec.1).trans (congrArg Ref.column hExpectedRef)
      obtain ⟨nodes, hNodes, hUpperRead⟩ := cellAt_ok_iff.mp
        (Canonical.cellAt_of_frame_node result upper)
      have hNodesEq : nodes = candidateCopy.column := Option.some.inj
        (hNodes.symm.trans (by
          change result[upper.1.val]? = some candidateCopy.column
          rw [hUpperColumn]
          exact candidateCopy.preserved.column_read (by simp)))
      subst nodes
      have hUpperHigh : p.lastTop.row ≤ (G.cell upper).row :=
        hHigh.trans ((hExpectedRow ▸ hHigher).le)
      obtain ⟨sourceIndex, sourceCell, hSourceRead, hRow⟩ :=
        candidateCopy.data.copyColumn_high_read_to_source
          (candidateCopy.state.marker_caps_below_lastTop hLast candidateCopy.data candidate.1.isLt)
          candidateCopy.read.copy_run hUpperRead hUpperHigh
      have hSourceColumn : p.reduced[candidate.1.val]? = some candidateCopy.data.sources :=
        (candidateCopy.state.base_ambient candidate.1.val candidate.1.isLt).symm.trans
          candidateCopy.data.source_column
      have hOtherRead : Canonical.cellAt p.reduced ⟨candidate.1.val, sourceIndex⟩ =
          .ok sourceCell :=
        cellAt_ok_iff.mpr ⟨candidateCopy.data.sources, hSourceColumn, hSourceRead⟩
      obtain ⟨other, hOtherRef, hOtherCell⟩ := Canonical.frame_node_of_cellAt hOtherRead
      have hOtherColumn : other.1 = candidate.1 := Fin.ext (congrArg Ref.column hOtherRef)
      have hOtherRow : F.height other = G.height upper := by
        change (F.cell other).row = (G.cell upper).row
        rw [hOtherCell, hRow]
      have hSourceReal : Frame.Real source := by
        by_contra hNot
        have hZero : source.2.val = 0 := by unfold Frame.Real at hNot; omega
        exact hUnmarked (List.mem_map.mpr
          ⟨⟨source.1.val, 0⟩, copy.data.phantom_marker, hZero.symm⟩)
      by_contra hNot
      have hBelow : F.height other ≤ F.height source := by
        rw [hOtherRow, ← hSourceRow]
        exact le_of_not_gt hNot
      have hMax := candidate_height_max hNormal.toOrdered hSourceReal hCandidate hOtherColumn hBelow
      rw [hOtherRow, ← hExpectedRow] at hMax
      exact not_lt_of_ge hMax hHigher
  rw [hColumns, hFront] at hExpectedFront
  have hActualRef : Frame.ref actualCandidate = candidateCopy.outputRef :=
    (congrArg Frame.ref hExpectedFront).trans hExpectedRef
  exact ⟨actualSource, actualCandidate, hSourceRef, hActualRef, hActualQ,
    by simpa only [hActualRef] using hSearch⟩

end EffectiveCopyOccurrence

/-- The physical-marker/effective-target distinction cannot occur at the
source Q candidate in this branch. Marker membership would force the source
child to the same marker row and give it a same-row path to the root prefix. -/
theorem Preparation.nonmarker_candidate
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {source candidate parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentRight : p.root.column < parent.1.val)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index) :
    candidate.2.val ∉ (p.marked[candidate.1.val]?.getD []).map Ref.index := by
  intro hMarkedIndex
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hCandidateReal := Frame.Q_real hNormal.toOrdered hSourceReal hCandidate
  obtain ⟨marked, hm, hi⟩ := List.mem_map.mp hMarkedIndex
  have hc := (p.marker_iff.mp hm).1
  have hMarkedRef : marked = Frame.ref candidate := by
    cases marked
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨hc, hi⟩
  have hMarked : BucketMem p.marked candidate.1.val (Frame.ref candidate) := hMarkedRef ▸ hm
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨hCandidateRight, low, hLowReal, hLowColumn, hLowIndex, hWhole, hRow⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hCandidateReal).mp hMarked
  have hCone : Frame.RootCone F low candidate :=
    ⟨candidate, hCandidateReal, rfl, hRow, hWhole⟩
  obtain ⟨_, candidateUpper, _, _, hUpper, hUpperRow⟩ :=
    hCone.successor_at_root hNormal hRow (by simpa only [hLowColumn] using hCandidateRight)
  have hLower : F.height low ≤ F.height source :=
    hRow ▸ Frame.Q_height_le hNormal.toOrdered hCandidate
  have hBefore : F.height source < Row.bump (F.height low) 0 :=
    (Frame.Q_upper_gt hNormal.toOrdered hCandidate hUpper).trans_eq hUpperRow
  have hSourceRow : F.height source = F.height low :=
    (Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero (Row.jump_le_of_lt_bump hLower hBefore))).symm
  obtain ⟨actualCandidate, hActualCandidate, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
  have hCandidateEq : actualCandidate = candidate :=
    Option.some.inj (hActualCandidate.symm.trans hCandidate)
  subst actualCandidate
  have hPath := trace.parentPath hNormal.toOrdered (hNormal.real_positive candidate hCandidateReal)
  have hRootColumn : root.1.val = p.root.column := congrArg Ref.column hRootRef
  have hTail := hPath.suffix_of_column_le hNormal.toOrdered hWhole
    (show low.1.val ≤ parent.1.val by rw [hLowColumn, hRootColumn]; exact hParentRight.le)
  have hSourceMarked :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hSourceReal).mpr
      ⟨by rw [hRootColumn]; exact hParentRight.trans (Frame.P_column_lt hNormal.toOrdered hParent),
        low, hLowReal, hLowColumn, hLowIndex, .cons hParent hTail, hSourceRow⟩
  exact hUnmarked (List.mem_map.mpr ⟨Frame.ref source, hSourceMarked, rfl⟩)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyRead.nonmarker_copy_execution
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_frontier
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_high
#print axioms OmegaY.Expansion.Preparation.nonmarker_candidate
