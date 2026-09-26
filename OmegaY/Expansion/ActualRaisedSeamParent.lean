/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRaisedSeamParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveContourParent
import OmegaY.Expansion.AdjacentMarkerExecution

/-!
# Effective source-parent edges across a raised marker seam

The next source marker is physically copied at its original row. Actual
reference caps prove that this is also the preceding marker's lifted upper
row. Thus the already established interval selector identifies the real
effective parent. No copied numerical normality or desired raw edge is an
input. The read-level theorem also includes consecutive source markers.
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

/-- Dynamic support also applies to an independently constructed local
data record: actual upper reads fix its parent reference and parent column.
Neither power steps nor the required low read of that parent is assumed. -/
theorem DynamicBlockState.column_data_parent_inputs
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hNext : next < p.reduced.size)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column) :
    NoPrematureOne d.sources ∧
      (∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes) ∧
      (∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
        (d.marker_data marker hm).parentNodes[index]? = some cell ∧
          cell.row = (d.marker_data marker hm).current.row) := by
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hEach : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes ∧
        ∃ (index : Nat) (cell : Cell), (d.marker_data marker hm).parentNodes[index]? = some cell ∧
          cell.row = (d.marker_data marker hm).current.row := by
    intro marker hm
    obtain ⟨actual⟩ := s.marker_data hLast hSource hm
    let md := d.marker_data marker hm
    have hCurrent : actual.current = md.current :=
      Option.some.inj (actual.current_at.symm.trans md.current_at)
    have hUpper : actual.upper = md.upper :=
      Option.some.inj (actual.upper_at.symm.trans md.upper_at)
    have hParent : actual.sourceParent = md.sourceParent := Option.some.inj
      (actual.upper_left.symm.trans (hUpper ▸ md.upper_left))
    have hNodes : actual.parentNodes = md.parentNodes := Option.some.inj
      (actual.parent_nodes.symm.trans (by simpa only [hParent] using md.parent_nodes))
    exact ⟨hNodes ▸ actual.parent_power, actual.lowIndex, actual.lowCell,
      by simpa only [hNodes] using actual.low_at, actual.low_row.trans (congrArg Cell.row hCurrent)⟩
  exact ⟨build_source_no_premature_one p.reduced_build hSource,
    fun marker hm => (hEach marker hm).1, fun marker hm => (hEach marker hm).2⟩

/-- A genuinely raised effective source whose successor is marked keeps
its actual source father at the father's effective occurrence. All support
for the supplied execution read is recovered from the dynamic state; the
parent occurrence is recovered from earlier actual copy executions. -/
theorem DynamicBlockState.actual_raised_seam_parent_of_read
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    {column : Column}
    (read : EffectiveCopyRead d child.2.val ((Frame.ofMountain p.reduced).cell child) column)
    (hUpperMarked : child.2.val + 1 ∈ d.bucket.map Ref.index)
    (hChildRaised : (Frame.ofMountain p.reduced).height child < read.outputCell.row) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (parentCopy : EffectiveCopyOccurrence p block start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      childCopy.outputRef = read.outputRef ∧
      RawRefEdge (ambient.push column) childCopy.outputRef parentCopy.outputRef := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  obtain ⟨hNoPremature, hParentPower, hParentLow⟩ :=
    s.column_data_parent_inputs hLast child.1.isLt d
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSource (congrArg Fin.val (Frame.upper_spec hUpper).1)
    simpa only [(Frame.upper_spec hUpper).2] using hRead
  have hUpperRef : Frame.ref sourceUpper = ⟨child.1.val, child.2.val + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  obtain ⟨upper, candidate, hUpperOut, _, hCopy, hShape⟩ :=
    d.effective_upper_marker_execution hParentPower hParentLow hNoPremature read hSourceUpper hUpperMarked
  let md := d.marker_data read.marker read.marker_mem
  have hLiftRaised : F.height child < Row.lift md.current.row md.targetCell.row (F.height child) := by
    simpa only [read.output_row, Frame.height, md, F] using hChildRaised
  obtain ⟨highMarker, hHighMember, hHighIndex⟩ := List.mem_map.mp hUpperMarked
  have hMarkerLt : read.marker.index < highMarker.index := by have := read.marker_before; omega
  have hHighCell : (d.marker_data highMarker hHighMember).current = F.cell sourceUpper :=
    Option.some.inj ((d.marker_data highMarker hHighMember).current_at.symm.trans
      (by simpa only [hHighIndex] using hSourceUpper))
  obtain ⟨degree, hTargetCap, hCap⟩ :=
    d.reference_caps read.marker read.marker_mem highMarker hHighMember hMarkerLt
  have hUpperFixed : Row.lift md.current.row md.targetCell.row (F.height sourceUpper) =
      F.height sourceUpper :=
    Row.lift_eq_of_ge_cap md.target_lower hTargetCap
      (by simpa only [hHighCell, Frame.height] using hCap)
  rcases s.marker_source_transport hLast d read.marker_mem rfl read.marker_before with
    ⟨_, hFixed⟩ | ⟨rootIndex, a, hActualTarget, hRaised, hChildInside | ⟨_, hFixed⟩⟩
  · exact False.elim ((ne_of_lt hLiftRaised) hFixed.symm)
  · have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
    have hRootRow : F.height a.root = md.current.row := a.root_row
    have hInside' : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) child := by
      simpa only [hRootRow] using hChildInside
    have hBarrier : ∀ rootUpper, F.upper a.root = some rootUpper →
        Row.bump (F.height a.root) a.degree ≤ F.height rootUpper := by
      simpa only [hRootRow] using a.root_upper_barrier
    have hParentInside : Frame.RootInterval F a.root (Row.bump md.current.row a.degree) parent := by
      rcases Frame.root_interval_parent_bump hNormal a.root_real (a.raised_degree hRaised)
          hBarrier hParent hInside' with hi | ⟨hb, _⟩
      · change Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) parent at hi
        simpa only [hRootRow] using hi
      · have hBefore := hb.1
        rw [hRootColumn] at hBefore
        omega
    obtain ⟨oldParentCopy⟩ := s.prior_effective_occurrence history hLast hRight
      (Frame.P_column_lt hNormal.toOrdered hParent)
    obtain ⟨copied, ref, parentCell, hActualCopy, _, _, hLeft, hColumn, hParentRead, hParentRow, _⟩ :=
      s.copyEdge_interval_parent history hLast a hRaised hChildInside hParent rfl hUpper
    have hCopy' : copyEdge ambient (Frame.ref sourceUpper)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift md.current.row a.target.row (F.height sourceUpper)) = .ok candidate := by
      rw [hUpperRef, hActualTarget, hUpperFixed]
      exact hCopy
    have hCopied : copied = candidate := Except.ok.inj (hActualCopy.symm.trans hCopy')
    subst copied
    have hNotFixed : ¬ parent.1.val < p.root.column := by omega
    have hActualColumn : ref.column = parent.1.val +
        block * (p.reduced.size - 1 - p.root.column) := by
      simpa only [if_neg hNotFixed] using hColumn
    have hActualRow : parentCell.row = oldParentCopy.read.outputCell.row := by
      rw [hParentRow, oldParentCopy.interval_row a hParentInside hRight]
      simp only [Frame.intervalParentRow, hRootColumn, if_neg hNotFixed, a.root_row]
    have hSelected : ref = oldParentCopy.outputRef := ref_eq_of_same_column_row s.ambient_valid
      hParentRead oldParentCopy.output_read (hActualColumn.trans oldParentCopy.source_column.symm) hActualRow
    let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
      ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
    let parentCopy := oldParentCopy.extend (PreservesColumns.push ambient column)
    refine ⟨childCopy, parentCopy, rfl, rfl, rfl, read.outputCell, upper,
      oldParentCopy.read.outputCell, read.output_read, ?_, ?_, parentCopy.output_read⟩
    · exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
        EffectiveCopyRead.outputRef], hUpperOut⟩
    · exact hShape.2.symm.trans (hSelected ▸ hLeft)
  · exact False.elim ((ne_of_lt hLiftRaised) hFixed.symm)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.column_data_parent_inputs
#print axioms OmegaY.Expansion.DynamicBlockState.actual_raised_seam_parent_of_read
