/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualPhysicalMarkerSearch.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualStationaryMarkerCandidate
import OmegaY.Expansion.CommonMarkerBands

/-!
# The physical marker's actual search start and outgoing stored parent

Physical marker occurrences retain the source row even when their effective
endpoints rise. Their reads and own-copy execution come from actual segments.
They are not identified with effective endpoints or vertical parent paths.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- An actual physical marker candidate, retained through finishing. -/
theorem ColumnCopyData.physical_marker_read
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) :
    ∃ (index : Nat) (cell copied : Cell), column[index]? = some cell ∧
      cell.row = (d.marker_data marker hm).current.row ∧
      copyEdge mountain ⟨sourceColumn, marker.index⟩ shift rootColumn
        (d.marker_data marker hm).current.row = .ok copied ∧ SameShape copied cell := by
  let md := d.marker_data marker hm
  obtain ⟨copied, path, gap, hResult, hCopy, _, _, _, _, _, _, _⟩ :=
    copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero
      d.destination.le d.source_top references (d.bucket.map Ref.index) md.current_at
      md.upper_at md.upper_left md.parent_nodes md.target_at md.reference md.target_lower
      (d.segment_run hm)
  have hCandidate : copied ∈ d.candidates := List.mem_flatMap.mpr
    ⟨marker, hm, by simp [hResult]⟩
  obtain ⟨index, cell, hCell, hShape⟩ := finish_candidate_read
    (d.copyColumn_eq_finish.symm.trans hRun) hCandidate
  exact ⟨index, cell, copied, hCell,
    hShape.1.symm.trans (copyEdge_return_row hCopy), hCopy, hShape⟩

/-- The physical marker's actual immediate upper points to the actual low
node of the copied source-parent column. Raised targets use the first fill
rung; stationary targets use the actual first-contour/next-marker seam. -/
theorem ColumnCopyData.physical_marker_upper
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (hPP : ∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hPL : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hUpper : (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0)
    (hRoot : rootColumn ≤ (d.marker_data marker hm).sourceParent.column)
    {lowIndex : Nat} {lowCell : Cell}
    (hLow : (d.marker_data marker hm).parentNodes[lowIndex]? = some lowCell)
    (hLowRow : lowCell.row = (d.marker_data marker hm).current.row)
    {index : Nat} {physical : Cell} (hRead : column[index]? = some physical)
    (hRow : physical.row = (d.marker_data marker hm).current.row) :
    ∃ upper, column[index + 1]? = some upper ∧
      upper.row = Row.bump (d.marker_data marker hm).current.row 0 ∧
      upper.left = some ⟨(d.marker_data marker hm).sourceParent.column + shift, lowIndex⟩ := by
  let md := d.marker_data marker hm
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  obtain ⟨hp, hParentEq⟩ := Array.getElem?_eq_some_iff.mp md.parent_nodes
  have hParentValid : ColumnValid mountain (md.sourceParent.column + shift) md.parentNodes :=
    hParentEq ▸ d.ambient_valid _ hp
  by_cases hRaised : md.current.row < md.targetCell.row
  · have hHead := fillCellsAscending_head hParentValid.rows_strict hLow md.target_at
      (show lowCell.row < md.targetCell.row by rw [hLowRow]; exact hRaised)
      (column := md.sourceParent.column + shift)
    rw [hLowRow] at hHead
    obtain ⟨before, after, copied, hCopiedRow, hSplit⟩ := d.marker_fill_splice hPP hPL hNoPremature hm
    have hFirst : (copied :: fillCellsAscending md.parentNodes (md.sourceParent.column + shift)
        md.current.row md.targetCell.row)[1]? =
        some (referenceRung md.current.row (md.sourceParent.column + shift) lowIndex 0) := by
      simpa only [List.getElem?_cons_succ, List.head?_eq_getElem?] using hHead
    obtain ⟨lower, upper, hLower, hUpperRead, hLowerShape, hUpperShape⟩ :=
      finish_adjacent_of_splice (d.copyColumn_eq_finish.symm.trans hRun) hSplit (index := 0) rfl hFirst
    simp only [Nat.add_zero] at hLower
    have hIndex := column_read_index_eq_of_row hValid hLower hRead
      ((hLowerShape.1.symm.trans hCopiedRow).trans hRow.symm)
    have hNext : before.length + (0 + 1) = index + 1 := by omega
    exact ⟨upper, by simpa only [hNext] using hUpperRead, hUpperShape.1.symm, hUpperShape.2.symm⟩
  · have hEqual : md.targetCell.row = md.current.row := le_antisymm (le_of_not_gt hRaised) md.target_lower
    have hTargetIndex := column_read_index_eq_of_row hParentValid md.target_at hLow
      (hEqual.trans hLowRow.symm)
    obtain ⟨upper, hUpperRead, hUpperRow, hUpperLeft⟩ := d.effective_marker_upper
      hPP hPL hNoPremature hRun hm hUpper hRoot hRead (hRow.trans hEqual.symm)
    change upper.row = Row.bump md.targetCell.row 0 at hUpperRow
    change upper.left = some ⟨md.sourceParent.column + shift, md.targetIndex⟩ at hUpperLeft
    rw [hEqual] at hUpperRow
    rw [hTargetIndex] at hUpperLeft
    exact ⟨upper, hUpperRead, hUpperRow, hUpperLeft⟩

/-- Only an actual column read and its original row are recorded. In
particular no search, stored-parent or numerical assertion is a field. -/
structure PhysicalMarkerRead {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref}
    {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
    (copy : EffectiveCopyOccurrence p block start references source result) where
  index : Nat
  cell : Cell
  output_at : copy.column[index]? = some cell
  source_row : cell.row = (Frame.ofMountain p.reduced).height source

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- Every true source marker has a physical output occurrence, including
when its effective endpoint is strictly higher. -/
theorem physical_marker_read
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source)) :
    Nonempty (PhysicalMarkerRead copy) := by
  let md := copy.data.marker_data (Frame.ref source) hMarked
  have hCurrent : md.current = (Frame.ofMountain p.reduced).cell source :=
    Option.some.inj (md.current_at.symm.trans copy.read.source_at)
  obtain ⟨index, cell, _, hRead, hRow, _, _⟩ :=
    copy.data.physical_marker_read copy.read.copy_run hMarked
  exact ⟨⟨index, cell, hRead, hRow.trans (congrArg Cell.row hCurrent)⟩⟩

end EffectiveCopyOccurrence

namespace PhysicalMarkerRead

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  {copy : EffectiveCopyOccurrence p block start references source result}
  (physical : PhysicalMarkerRead copy)

def outputRef : Ref := ⟨copy.before.size, physical.index⟩

theorem output_read : Canonical.cellAt result physical.outputRef = .ok physical.cell := by
  rw [copy.preserved.cellAt (show physical.outputRef.column < (copy.before.push copy.column).size by
    simp [outputRef])]
  exact cellAt_ok_iff.mpr ⟨copy.column, by simp [outputRef], physical.output_at⟩

theorem source_column : physical.outputRef.column =
    source.1.val + block * (p.reduced.size - 1 - p.root.column) := copy.state.size_eq

theorem own_copy_execution
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source)) :
    ∃ copied, copyEdge copy.before (Frame.ref source)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      physical.cell.row = .ok copied ∧ SameShape copied physical.cell := by
  let md := copy.data.marker_data (Frame.ref source) hMarked
  have hCurrent : md.current = (Frame.ofMountain p.reduced).cell source :=
    Option.some.inj (md.current_at.symm.trans copy.read.source_at)
  obtain ⟨index, cell, copied, hRead, hRow, hCopy, hShape⟩ :=
    copy.data.physical_marker_read copy.read.copy_run hMarked
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := copy.data.copyColumn_valid
  have he : actual = copy.column := Except.ok.inj (hActual.symm.trans copy.read.copy_run)
  subst actual
  have hIndex := column_read_index_eq_of_row hValid hRead physical.output_at
    ((hRow.trans (congrArg Cell.row hCurrent)).trans physical.source_row.symm)
  have hCell : cell = physical.cell :=
    Option.some.inj (hRead.symm.trans (hIndex ▸ physical.output_at))
  refine ⟨copied, ?_, hCell ▸ hShape⟩
  have hRowEq : md.current.row = physical.cell.row :=
    (congrArg Cell.row hCurrent).trans physical.source_row.symm
  change copyEdge copy.before (Frame.ref source)
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column md.current.row = .ok copied at hCopy
  rw [hRowEq] at hCopy
  exact hCopy

/-- Actual Q at the original physical row is the inclusive frontier of
the translated old-Q column, irrespective of the effective target height. -/
theorem candidate_frontier (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    (hReal : Frame.Real source)
    {candidate : (Frame.ofMountain p.reduced).Node}
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hMoved : p.root.column ≤ candidate.1.val) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = physical.outputRef ∧
      (Frame.ofMountain result).cell actualSource = physical.cell ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result physical.outputRef = .ok (Frame.ref actualCandidate) ∧
      actualCandidate.1.val = candidate.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      ∃ hCut : (1 : Row) ≤ physical.cell.row,
        Frame.frontierAt hValid.toOrdered physical.cell.row hCut actualCandidate.1 =
          actualCandidate := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨copied, hCopy, hShape⟩ := physical.own_copy_execution hMarked
  have hSourceRead : lookup copy.before (Frame.ref source) = .ok (F.cell source) :=
    lookup_ok_iff.mpr ⟨copy.data.sources, copy.data.source_column, copy.read.source_at⟩
  have hPositive : (0 : Row) < (F.cell source).row :=
    Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hReal)
  have hPhysicalPositive : (0 : Row) < physical.cell.row := by
    rw [physical.source_row]
    exact hPositive
  obtain ⟨expected, parentRef, parentCell, hExpected, _, _, hExpectedLeft,
      hParentRead, hParentColumn, oldParent, hOldLeft, _, hEndpoint⟩ :=
    copyEdge_nonphantom_total copy.data.ambient_valid hSourceRead copy.data.source_nonzero
      copy.data.destination.le (ne_of_gt hPositive)
      hPhysicalPositive
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
    Canonical.frame_node_of_cellAt physical.output_read
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
  have hCut : (1 : Row) ≤ physical.cell.row := by
    rw [physical.source_row]
    exact Frame.one_le_height hNormal.toOrdered hReal
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

/-- The genuine new Q is the physical old-Q marker. In particular this does
not identify it with the old-Q effective endpoint when that endpoint rises. -/
theorem candidate_eq (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    {candidateCopy : EffectiveCopyOccurrence p block start references candidate result}
    (candidatePhysical : PhysicalMarkerRead candidateCopy)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentRight : p.root.column < parent.1.val) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = physical.outputRef ∧
      Frame.ref actualCandidate = candidatePhysical.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result physical.outputRef = .ok candidatePhysical.outputRef := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨_, hSourceRows⟩ := build_marked_candidate p.reduced_build hMarkers
    hParent hCandidate hMarked ((congrArg Ref.column hRootRef).trans_lt hParentRight)
  have hOutputRows : candidatePhysical.cell.row = physical.cell.row :=
    candidatePhysical.source_row.trans (hSourceRows.trans physical.source_row.symm)
  obtain ⟨actual, hActual, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
  have he : actual = candidate := Option.some.inj (hActual.symm.trans hCandidate)
  subst actual
  have hCandidateReal := Frame.Q_real hNormal.toOrdered hReal hCandidate
  have hPath := trace.parentPath hNormal.toOrdered (hNormal.real_positive candidate hCandidateReal)
  have hMoved := hParentRight.trans_le (hPath.column_le hNormal.toOrdered)
  obtain ⟨actualSource, actualCandidate, hSourceRef, _, hActualQ, hSearch,
      hColumn, hCut, hFront⟩ := physical.candidate_frontier hValid hMarked hReal hCandidate hMoved.le
  obtain ⟨expected, hExpectedRef, hExpectedCell⟩ :=
    Canonical.frame_node_of_cellAt candidatePhysical.output_read
  have hExpectedRow : G.height expected = physical.cell.row := by
    change (G.cell expected).row = _
    rw [hExpectedCell, hOutputRows]
  have hColumns : expected.1 = actualCandidate.1 := Fin.ext
    ((congrArg Ref.column hExpectedRef).trans candidatePhysical.source_column |>.trans hColumn.symm)
  have hExpectedFront : Frame.frontierAt hValid.toOrdered physical.cell.row hCut expected.1 = expected := by
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
  have hActualRef : Frame.ref actualCandidate = candidatePhysical.outputRef :=
    (congrArg Frame.ref hExpectedFront).trans hExpectedRef
  exact ⟨actualSource, actualCandidate, hSourceRef, hActualRef, hActualQ,
    by simpa only [hActualRef] using hSearch⟩

/-- Source numerical parenthood gives the actual physical copied raw edge,
for raised and stationary markers alike. The successor height and both
real endpoint reads are consequences of the actual fill/contour execution. -/
theorem raw_parent (hLast : 1 < last) (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {parent : (Frame.ofMountain p.reduced).Node}
    {parentCopy : EffectiveCopyOccurrence p block start references parent result}
    (parentPhysical : PhysicalMarkerRead parentCopy)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hRight : p.root.column < parent.1.val) :
    RawRefEdge result physical.outputRef parentPhysical.outputRef ∧
      ∃ upper, Canonical.cellAt result ⟨physical.outputRef.column, physical.outputRef.index + 1⟩ = .ok upper ∧
        upper.row = Row.bump physical.cell.row 0 := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  let md := d.marker_data (Frame.ref source) hMarked
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hSources : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hCurrent : md.current = F.cell source := Option.some.inj
    (md.current_at.symm.trans copy.read.source_at)
  obtain ⟨sourceUpper, hSourceUpper⟩ := hNormal.upper_of_parent hParent
  have hUpperAt : d.sources[source.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSources (congrArg Fin.val (Frame.upper_spec hSourceUpper).1)
    simpa only [(Frame.upper_spec hSourceUpper).2] using hRead
  have hUpperCell : md.upper = F.cell sourceUpper := Option.some.inj (md.upper_at.symm.trans hUpperAt)
  obtain ⟨actualParent, hActualParent, hB, _, hStored⟩ := hNormal.upper_step source sourceUpper hReal hSourceUpper
  have he : actualParent = parent := Option.some.inj (hActualParent.symm.trans hParent)
  subst actualParent
  have hSourceParent : md.sourceParent = Frame.ref parent := Option.some.inj
    (md.upper_left.symm.trans (by simpa only [hUpperCell] using hStored))
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨_, hSameRows⟩ := build_marked_parent p.reduced_build hMarkers hParent hMarked
    ((congrArg Ref.column hRootRef).trans_lt hRight)
  have hSourceUpperRow : md.upper.row = Row.bump md.current.row 0 := by
    rw [hUpperCell, hCurrent]
    change F.height sourceUpper = Row.bump (F.height source) 0
    change F.height sourceUpper = Row.B (F.height source) (F.height parent) at hB
    have hSame : F.height source = F.height parent := hSameRows
    simpa only [← hSame, Row.B_self] using hB
  have hRoot : p.root.column ≤ md.sourceParent.column := by
    rw [hSourceParent]
    exact hRight.le
  obtain ⟨hNoPremature, hPP, hPL⟩ := copy.state.column_data_parent_inputs hLast source.1.isLt d
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hPL (Frame.ref source) hMarked
  have hPhysicalRow : physical.cell.row = md.current.row :=
    physical.source_row.trans (congrArg Cell.row hCurrent).symm
  obtain ⟨upper, hUpperRead, hUpperRow, hUpperLeft⟩ := d.physical_marker_upper
    hPP hPL hNoPremature copy.read.copy_run hMarked hSourceUpperRow hRoot hLow hLowRow
    physical.output_at hPhysicalRow
  let lowRef : Ref := ⟨md.sourceParent.column + block * (p.reduced.size - 1 - p.root.column), lowIndex⟩
  have hLowRead : Canonical.cellAt copy.before lowRef = .ok lowCell :=
    cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, hLow⟩
  have hLowBound : lowRef.column < copy.before.size := (Array.getElem?_eq_some_iff.mp md.parent_nodes).1
  have hPreserve : PreservesColumns copy.before result :=
    (PreservesColumns.push copy.before copy.column).trans copy.preserved
  have hLowResult : Canonical.cellAt result lowRef = .ok lowCell := (hPreserve.cellAt hLowBound).trans hLowRead
  obtain ⟨actualLow, hLowRef, hLowCell⟩ := Canonical.frame_node_of_cellAt hLowResult
  obtain ⟨actualParent, hParentRef, hParentCell⟩ := Canonical.frame_node_of_cellAt parentPhysical.output_read
  have hColumn : lowRef.column = parentPhysical.outputRef.column := by
    change md.sourceParent.column + _ = _
    rw [hSourceParent, parentPhysical.source_column]
    rfl
  have hRow : lowCell.row = parentPhysical.cell.row :=
    hLowRow.trans ((congrArg Cell.row hCurrent).trans (hSameRows.trans parentPhysical.source_row.symm))
  have hNodes : actualLow = actualParent := Frame.node_eq_of_column_height hValid.toOrdered
    (Fin.ext ((congrArg Ref.column hLowRef).trans (hColumn.trans (congrArg Ref.column hParentRef).symm)))
    (by simpa only [Frame.height, hLowCell, hParentCell] using hRow)
  have hRef : lowRef = parentPhysical.outputRef :=
    hLowRef.symm.trans ((congrArg Frame.ref hNodes).trans hParentRef)
  have hActualUpper : Canonical.cellAt result
      ⟨physical.outputRef.column, physical.outputRef.index + 1⟩ = .ok upper := by
    exact (copy.preserved.cellAt
      (ref := ⟨physical.outputRef.column, physical.outputRef.index + 1⟩)
      (by simp [outputRef])).trans
      (cellAt_ok_iff.mpr ⟨copy.column, by simp [outputRef], hUpperRead⟩)
  have hActualLeft : upper.left = some parentPhysical.outputRef :=
    hUpperLeft.trans (congrArg some hRef)
  exact ⟨⟨physical.cell, upper, parentPhysical.cell, physical.output_read, hActualUpper,
    hActualLeft, parentPhysical.output_read⟩,
    upper, hActualUpper, hUpperRow.trans (congrArg (fun row => Row.bump row 0) hPhysicalRow.symm)⟩

end PhysicalMarkerRead
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.physical_marker_read
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.physical_marker_read
#print axioms OmegaY.Expansion.PhysicalMarkerRead.own_copy_execution
#print axioms OmegaY.Expansion.PhysicalMarkerRead.candidate_frontier
#print axioms OmegaY.Expansion.PhysicalMarkerRead.candidate_eq
#print axioms OmegaY.Expansion.ColumnCopyData.physical_marker_upper
#print axioms OmegaY.Expansion.PhysicalMarkerRead.raw_parent
