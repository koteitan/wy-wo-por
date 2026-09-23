/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveCopy
import OmegaY.Expansion.ActualHighEdge
import OmegaY.Expansion.ContourAdjacent
import OmegaY.Expansion.ContourExecutionAt
import OmegaY.Expansion.FillRecordPath

/-!
# Actual effective parent edges in the unchanged high tail

Only the original source graph is normal. Actual contour calls, finishing,
and prior-copy history identify both copied endpoints. The result concerns
stored raw edges, not a postulated numerical parent of the copied mountain.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem contour_source_read {nodes : Column} {markers : List Nat}
    {index position : Nat} {current cell : Cell}
    (hRead : (contourSourceCells markers index current
      (nodes.toList.drop (index + 1)))[position]? = some cell) :
    nodes[index + position + 1]? = some cell := by
  rw [contourSourceCells_eq_take, List.getElem?_take] at hRead
  split at hRead
  · simpa only [List.getElem?_drop, Array.getElem?_toList,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hRead
  · cases hRead

/-- The adjacent output nodes retain the actual upper copy call and its
stored-left equality, as well as both common-lift row equations. -/
theorem ColumnCopyData.copyColumn_source_adjacent_execution
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {oldLower oldUpper : Cell}
    (hLower : d.sources[sourceIndex]? = some oldLower)
    (hUpper : d.sources[sourceIndex + 1]? = some oldUpper)
    (hAfter : marker.index < sourceIndex)
    (hNoBetween : ∀ middle, marker.index < middle → middle ≤ sourceIndex + 1 →
      middle ∉ d.bucket.map Ref.index) :
    ∃ (position : Nat) (lower upper copiedUpper : Cell),
      column[position]? = some lower ∧ column[position + 1]? = some upper ∧
      lower.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldLower.row ∧
      upper.row = Row.lift (d.marker_data marker hm).current.row
        (d.marker_data marker hm).targetCell.row oldUpper.row ∧
      copyEdge mountain ⟨sourceColumn, sourceIndex + 1⟩ shift rootColumn
        (Row.lift (d.marker_data marker hm).current.row
          (d.marker_data marker hm).targetCell.row oldUpper.row) = .ok copiedUpper ∧
      SameShape copiedUpper upper := by
  let md := d.marker_data marker hm
  obtain ⟨index, hLo, hHi⟩ := contourSourceCells_pair_of_no_between hNoPremature
    (d.bucket.map Ref.index) md.current_at hLower hUpper hAfter hNoBetween rfl
  have hSourceLow := contour_source_read hLo
  have hIndex : marker.index + index + 1 = sourceIndex :=
    column_read_index_eq_of_row d.source_valid hSourceLow hLower rfl
  obtain ⟨path, before, after, hPath, hSplit⟩ :=
    d.contour_splice_in_candidates hParentPower hParentLow hNoPremature hm
  have hRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column d.source_nonzero
    d.destination.le d.source_top d.source_power (d.bucket.map Ref.index)
    md.targetCell.row md.current_at rfl hPath
  have hLowerRow : (path.map Cell.row)[index]? =
      some (Row.lift md.current.row md.targetCell.row oldLower.row) := by
    rw [hRows]
    simp only [List.getElem?_map, hLo, Option.map_some, md]
  have hUpperRow : (path.map Cell.row)[index + 1]? =
      some (Row.lift md.current.row md.targetCell.row oldUpper.row) := by
    rw [hRows]
    simp only [List.getElem?_map, hHi, Option.map_some, md]
  obtain ⟨copiedLower, hCopiedLower, hCopiedLowerRow⟩ := cell_read_of_row_read hLowerRow
  obtain ⟨copiedUpper, hCopiedUpper, hCopiedUpperRow⟩ := cell_read_of_row_read hUpperRow
  obtain ⟨execution⟩ := d.contour_inside_source hm hPath hCopiedLower hCopiedUpper
  have hSourceUpper : execution.upper = oldUpper := Option.some.inj
    (execution.upper_at.symm.trans (by
      simpa only [show marker.index + index + 2 = sourceIndex + 1 by omega] using hUpper))
  obtain ⟨lower, upper, hLowerOut, hUpperOut, hLowerShape, hUpperShape⟩ :=
    finish_adjacent_of_splice (d.copyColumn_eq_finish.symm.trans hRun) hSplit hCopiedLower hCopiedUpper
  exact ⟨before.length + index, lower, upper, copiedUpper, hLowerOut, hUpperOut,
    hLowerShape.1.symm.trans hCopiedLowerRow, hUpperShape.1.symm.trans hCopiedUpperRow,
    by simpa only [show marker.index + index + 2 = sourceIndex + 1 by omega,
      hSourceUpper] using execution.upper_copy, hUpperShape⟩

/-- All high effective occurrences have their original row, including an
occurrence constructed in a previous actual copy state. -/
theorem DynamicBlockState.effective_high_row
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hNext : next < p.reduced.size)
    {d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column}
    {sourceIndex : Nat} {sourceCell : Cell} {column : Column}
    (read : EffectiveCopyRead d sourceIndex sourceCell column)
    (hHigh : p.lastTop.row ≤ sourceCell.row) : read.outputCell.row = sourceCell.row := by
  obtain ⟨degree, hTarget, hCap⟩ :=
    s.marker_caps_below_lastTop hLast d hNext read.marker read.marker_mem
  rw [read.output_row]
  exact Row.lift_eq_of_ge_cap (d.marker_data read.marker read.marker_mem).target_lower
    hTarget (hCap.trans hHigh)

theorem DynamicBlockState.high_source_not_marked
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hNext : next < p.reduced.size)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    {sourceIndex : Nat} {sourceCell : Cell}
    (hSource : d.sources[sourceIndex]? = some sourceCell)
    (hHigh : p.lastTop.row ≤ sourceCell.row) : sourceIndex ∉ d.bucket.map Ref.index := by
  intro hMem
  obtain ⟨marker, hm, hIndex⟩ := List.mem_map.mp hMem
  obtain ⟨degree, hTarget, hCap⟩ := s.marker_caps_below_lastTop hLast d hNext marker hm
  have hCell : (d.marker_data marker hm).current = sourceCell := Option.some.inj
    ((d.marker_data marker hm).current_at.symm.trans (by simpa only [hIndex] using hSource))
  have hBelow := ((d.marker_data marker hm).target_lower.trans_lt hTarget).trans_le hCap
  rw [hCell] at hBelow
  exact (not_lt_of_ge hHigh) hBelow

/-- For a high effective source with an actual successor, the actual
successor of its output occurrence is the executed copy of that source
successor. In particular no fill or another marker intervenes. -/
theorem DynamicBlockState.effective_high_upper_execution
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hNext : next < p.reduced.size)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources)
    {sourceIndex : Nat} {sourceCell sourceUpper : Cell} {column : Column}
    (read : EffectiveCopyRead d sourceIndex sourceCell column)
    (hUpper : d.sources[sourceIndex + 1]? = some sourceUpper)
    (hHigh : p.lastTop.row ≤ sourceCell.row) :
    ∃ upper copied,
      column[read.outputIndex + 1]? = some upper ∧
      upper.row = sourceUpper.row ∧
      copyEdge ambient ⟨next, sourceIndex + 1⟩
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column sourceUpper.row = .ok copied ∧
      SameShape copied upper := by
  have hSourceRows := d.source_valid.rows_strict _ _ _ _ read.source_at hUpper (Nat.lt_succ_self _)
  have hHighUpper := hHigh.trans hSourceRows.le
  have hNotMarked := s.high_source_not_marked hLast hNext d read.source_at hHigh
  have hUpperNotMarked := s.high_source_not_marked hLast hNext d hUpper hHighUpper
  have hAfter : read.marker.index < sourceIndex := by
    have hMember : read.marker.index ∈ d.bucket.map Ref.index :=
      List.mem_map.mpr ⟨read.marker, read.marker_mem, rfl⟩
    have hNe : read.marker.index ≠ sourceIndex := fun he => hNotMarked (he ▸ hMember)
    have hBefore := read.marker_before
    omega
  have hNoBetween : ∀ middle, read.marker.index < middle → middle ≤ sourceIndex + 1 →
      middle ∉ d.bucket.map Ref.index := by
    intro middle hLow hUpperBound
    by_cases hLe : middle ≤ sourceIndex
    · exact read.no_between middle hLow hLe
    · have he : middle = sourceIndex + 1 := by omega
      exact he ▸ hUpperNotMarked
  obtain ⟨position, lower, upper, copied, hLo, hHi, hLoRow, hHiRow, hCopy, hShape⟩ :=
    d.copyColumn_source_adjacent_execution hParentPower hParentLow hNoPremature read.copy_run
      read.marker_mem read.source_at hUpper hAfter hNoBetween
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans read.copy_run)
  subst actual
  have hIndex : position = read.outputIndex :=
    column_read_index_eq_of_row hValid hLo read.output_at (hLoRow.trans read.output_row.symm)
  obtain ⟨degree, hTarget, hCap⟩ :=
    s.marker_caps_below_lastTop hLast d hNext read.marker read.marker_mem
  have hFixed : Row.lift (d.marker_data read.marker read.marker_mem).current.row
      (d.marker_data read.marker read.marker_mem).targetCell.row sourceUpper.row = sourceUpper.row :=
    Row.lift_eq_of_ge_cap (d.marker_data read.marker read.marker_mem).target_lower hTarget
      (hCap.trans hHighUpper)
  exact ⟨upper, copied, hIndex ▸ hHi, hHiRow.trans hFixed,
    by simpa only [hFixed] using hCopy, hShape⟩

/-- An effective occurrence remembers the real earlier state and execution,
with complete-column preservation into the mountain where it is queried. -/
structure EffectiveCopyOccurrence {front : List Nat} {last : Nat} (p : Preparation front last)
    (block : Nat) (start : Mountain) (references : List Ref)
    (source : (Frame.ofMountain p.reduced).Node) (result : Mountain) where
  before : Mountain
  column : Column
  state : DynamicBlockState p block start references source.1.val before
  data : ColumnCopyData before p.marked references source.1.val
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column
  read : EffectiveCopyRead data source.2.val ((Frame.ofMountain p.reduced).cell source) column
  preserved : PreservesColumns (before.push column) result

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

def outputRef : Ref := copy.read.outputRef

theorem output_read : Canonical.cellAt result copy.outputRef = .ok copy.read.outputCell := by
  obtain ⟨nodes, hColumn, hCell⟩ := cellAt_ok_iff.mp copy.read.output_read
  exact cellAt_ok_iff.mpr ⟨nodes, copy.preserved.column_read hColumn, hCell⟩

theorem source_column : copy.outputRef.column =
    source.1.val + block * (p.reduced.size - 1 - p.root.column) := copy.read.output_source_column

theorem high_row (hLast : 1 < last)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source) :
    copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source :=
  copy.state.effective_high_row hLast source.1.isLt copy.read hHigh

def extend {after : Mountain} (h : PreservesColumns result after) :
    EffectiveCopyOccurrence p block start references source after :=
  { copy with preserved := copy.preserved.trans h }

end EffectiveCopyOccurrence

/-- Earlier effective occurrences are constructed from the actual copy
history; neither the occurrence nor its controlling marker is an input. -/
theorem DynamicBlockState.prior_effective_occurrence
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {source : (Frame.ofMountain p.reduced).Node}
    (hRight : p.root.column < source.1.val) (hBefore : source.1.val < next) :
    Nonempty (EffectiveCopyOccurrence p block start references source ambient) := by
  obtain ⟨before, column, oldState, hRun, hPreserve, _⟩ := history.column_read hRight hBefore
  have hSourceBound : source.1.val < p.reduced.size := hBefore.trans_le s.next_upper
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := oldState.column_data hLast hSourceBound
  have hSource : p.reduced[source.1.val]? = some d.sources :=
    (oldState.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hRead : d.sources[source.2.val]? = some ((Frame.ofMountain p.reduced).cell source) := by
    have hArray := (Array.getElem?_eq_some_iff.mp hSource).2
    rw [← hArray]
    exact Array.getElem?_eq_getElem source.2.isLt
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hRead
  exact ⟨⟨before, column, oldState, d, read, hPreserve⟩⟩

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

/-- The complete high-parent case. Both effective occurrences are built
from the real current run and earlier-copy history. The stored parent of
the actual child occurrence is exactly the same-block effective occurrence
of its numerical source parent, even when their controlling markers differ. -/
theorem DynamicBlockState.actual_high_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (parentCopy : EffectiveCopyOccurrence p block start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef parentCopy.outputRef := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  have hParentLeft := Frame.P_column_lt hNormal.toOrdered hParent
  have hParentLe := Frame.P_height_le hNormal.toOrdered hParent
  have hChildHigh := hHigh.trans hParentLe
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead : d.sources[child.2.val]? = some (F.cell child) := by
    have hArray := (Array.getElem?_eq_some_iff.mp hSource).2
    rw [← hArray]
    exact Array.getElem?_eq_getElem child.2.isLt
  have hUpperRef : Frame.ref sourceUpper = ⟨child.1.val, child.2.val + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
    obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp
      (cellAt_of_frame_node p.reduced sourceUpper)
    rw [hUpperRef] at hNodes hRead
    have he : nodes = d.sources := Option.some.inj (hNodes.symm.trans hSource)
    exact he ▸ hRead
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
  obtain ⟨upper, copied, hUpperOut, _, hCopy, hShape⟩ :=
    s.effective_high_upper_execution hLast child.1.isLt d hParentPower hParentLow
      hNoPremature read hSourceUpper hChildHigh
  obtain ⟨oldParentCopy⟩ := s.prior_effective_occurrence history hLast hRight hParentLeft
  have hExecutable : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent) :=
    (Executable.findParent_ref_iff hNormal.toOrdered child parent).mpr hParent
  obtain ⟨ref, parentCell, hBelow, hParentRead, hColumn, hRow⟩ :=
    s.below_high_parent history hLast hExecutable rfl hUpper hRight hHigh
  have hSelected : ref = oldParentCopy.outputRef := ref_eq_of_same_column_row s.ambient_valid
    hParentRead oldParentCopy.output_read (hColumn.trans oldParentCopy.source_column.symm)
    (hRow.trans (oldParentCopy.high_row hLast hHigh).symm)
  rw [hSelected] at hBelow
  have hChildReal : Frame.Real child := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldParent, hOldParent, _, _, hStored⟩ := hNormal.upper_step child sourceUpper hChildReal hUpper
  have he : oldParent = parent := Option.some.inj (hOldParent.symm.trans hParent)
  subst oldParent
  change (F.cell sourceUpper).left = some (Frame.ref parent) at hStored
  have hLookup : lookup ambient ⟨child.1.val, child.2.val + 1⟩ = .ok (F.cell sourceUpper) :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, hSourceUpper⟩
  have hUpperNonzero : (F.cell sourceUpper).row ≠ 0 := by
    have hPositive := Frame.one_le_height hNormal.toOrdered (upper_real hUpper)
    intro hz
    change (1 : Row) ≤ (F.cell sourceUpper).row at hPositive
    rw [hz] at hPositive
    exact (not_le_of_gt Row.zero_lt_one) hPositive
  have hNotFixed : ¬ (Frame.ref parent).column < p.root.column := by
    change ¬ parent.1.val < p.root.column
    omega
  have hDestination : oldParentCopy.outputRef.column < child.1.val +
      block * (p.reduced.size - 1 - p.root.column) := by
    rw [oldParentCopy.source_column]
    exact Nat.add_lt_add_right hParentLeft _
  change below ambient ((Frame.ref parent).column +
    block * (p.reduced.size - 1 - p.root.column)) (F.cell sourceUpper).row =
      .ok oldParentCopy.outputRef at hBelow
  have hCopied : (⟨(F.cell sourceUpper).row, 0, some oldParentCopy.outputRef⟩ : Cell) = copied := by
    simpa [copyEdge, hLookup, hUpperNonzero, leftOf, hStored, hNotFixed,
      hBelow, Nat.not_le_of_gt hDestination] using hCopy
  have hCopiedLeft : copied.left = some oldParentCopy.outputRef :=
    congrArg Cell.left hCopied.symm
  let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
    ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
  let parentCopy := oldParentCopy.extend (PreservesColumns.push ambient column)
  refine ⟨childCopy, parentCopy, rfl, rfl, read.outputCell, upper,
    oldParentCopy.read.outputCell, read.output_read, ?_, hShape.2.symm.trans hCopiedLeft,
    parentCopy.output_read⟩
  exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
    EffectiveCopyRead.outputRef], hUpperOut⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_source_adjacent_execution
#print axioms OmegaY.Expansion.DynamicBlockState.effective_high_row
#print axioms OmegaY.Expansion.DynamicBlockState.effective_high_upper_execution
#print axioms OmegaY.Expansion.DynamicBlockState.prior_effective_occurrence
#print axioms OmegaY.Expansion.DynamicBlockState.actual_high_effective_parent
