/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualStationaryEffectiveParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveContourParent
import OmegaY.Expansion.DynamicInactiveParent
import OmegaY.Expansion.DynamicActiveParent
import OmegaY.Expansion.ActualMarkerParentEdge
import OmegaY.Expansion.InheritedMarkers
import OmegaY.Expansion.EffectiveOccurrenceUnique
import OmegaY.Expansion.AdjacentMarkerExecution

/-!
# Exact effective fathers of stationary source contours

The parent's own real controlling marker determines whether its effective
row is stationary or lifted. A stationary child does not imply a stationary
parent. All previous-copy data and interval certificates are constructed
from actual state and history; copied numerical normality is absent.
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

/-- The real strict-below selector at a stationary source upper returns
the exact effective occurrence of its source father. The father is allowed
to rise in a different, lower marker interval. -/
theorem DynamicBlockState.below_stationary_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    {childMarker : Ref} (hcm : childMarker ∈ d.bucket)
    (hAfter : childMarker.index ≤ child.2.val)
    (hNoBetween : ∀ middle, childMarker.index < middle → middle ≤ child.2.val →
      middle ∉ d.bucket.map Ref.index)
    (hStationary : Row.lift (d.marker_data childMarker hcm).current.row
      (d.marker_data childMarker hcm).targetCell.row ((Frame.ofMountain p.reduced).height child) =
        (Frame.ofMountain p.reduced).height child) :
    ∃ parentCopy : EffectiveCopyOccurrence p block start references parent ambient,
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        ((Frame.ofMountain p.reduced).height upper) = .ok parentCopy.outputRef := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hNext : next < p.reduced.size := hChildColumn ▸ child.1.isLt
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hBefore : parent.1.val < next := by
    simpa only [hChildColumn] using Frame.P_column_lt hNormal.toOrdered hParent
  obtain ⟨copy⟩ := s.prior_effective_occurrence history hLast hRight hBefore
  let pd := copy.data
  let marker := copy.read.marker
  have hm : marker ∈ pd.bucket := copy.read.marker_mem
  let md := pd.marker_data marker hm
  have hParentSource : p.reduced[parent.1.val]? = some pd.sources :=
    (copy.state.base_ambient parent.1.val parent.1.isLt).symm.trans pd.source_column
  have hRead : Canonical.cellAt p.reduced marker = .ok md.current :=
    cellAt_ok_iff.mpr ⟨pd.sources, by simpa only [pd.marker_columns marker hm] using hParentSource,
      md.current_at⟩
  have hReference : referenceAt start references md.current.row = .ok md.targetCell.row :=
    (copy.state.referenceAt_preserved md.current.row).symm.trans md.reference
  have hAmbientReference : referenceAt ambient references md.current.row = .ok md.targetCell.row :=
    (s.referenceAt_preserved md.current.row).trans hReference
  have hLower : md.current.row ≤ F.height parent := copy.read.source_lower
  obtain ⟨actualMarker, hMarkerRef, hMarkerCell⟩ := frame_node_of_cellAt (cellAt_ok_iff.mp hRead)
  have hMarkerColumn : actualMarker.1.val = parent.1.val :=
    (congrArg Ref.column hMarkerRef).trans (pd.marker_columns marker hm)
  have hMember : BucketMem p.marked actualMarker.1.val (Frame.ref actualMarker) := by
    rw [hMarkerColumn, hMarkerRef]
    exact hm
  have hMarkerRow : F.height actualMarker = md.current.row := congrArg Cell.row hMarkerCell
  have hSelected : ∃ (ref : Ref) (cell : Cell),
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        (F.height upper) = .ok ref ∧ Canonical.cellAt ambient ref = .ok cell ∧
      ref.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      cell.row = copy.read.outputCell.row := by
    rcases eq_or_lt_of_le hLower with hSame | hAbove
    · have hPositive : 0 < md.current.row := by
        rw [hSame]
        exact Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered
          (Frame.real_of_value_pos hNormal.toOrdered (Frame.P_value hNormal.toOrdered hParent).1))
      obtain ⟨rootIndex, ⟨a⟩⟩ := s.actual_marker_root_interval hLast hm hRead hPositive
      have hCone : Frame.RootCone F a.root parent :=
        (a.rootCone_of_marker hMember hMarkerRow).same_column (Fin.ext hMarkerColumn)
      have hInside : Frame.RootInterval F a.root (Row.bump md.current.row a.degree) parent := by
        refine ⟨hCone, ?_, ?_⟩
        · exact a.root_row.trans_le hLower
        · rw [← hSame]
          exact Row.lt_bump _ _
      have hFixed := d.stationary_child_for_active_parent hSource a hcm hParent hInside
        hChildColumn s.next_lower hAfter hNoBetween hUpper hStationary
      obtain ⟨ref, cell, hBelow, hCell, hColumn, hRow⟩ := s.below_stationary_marker_parent
        a hParent hCone hSame.symm hChildColumn hRight hUpper hFixed.1
      obtain ⟨_, _, hTargetFixed⟩ := a.stationary_marker_parent_rows hParent hCone hSame.symm
        hRight hUpper hFixed.1
      have hCopyRow : copy.read.outputCell.row = F.height parent := by
        rw [copy.interval_row a hInside hRight, hTargetFixed]
        exact Row.lift_identity hLower
      exact ⟨ref, cell, hBelow, hCell, hColumn, hRow.trans hCopyRow.symm⟩
    · by_cases hRaised : md.current.row < md.targetCell.row
      · obtain ⟨rootIndex, a, hTarget, _⟩ :=
          s.raised_marker_root_interval hLast hm hRead hAmbientReference hRaised
        by_cases hInsideHeight : F.height parent < Row.bump md.current.row a.degree
        · have hInside : Frame.RootInterval F a.root (Row.bump md.current.row a.degree) parent :=
            a.inside_of_marker hMember hMarkerRow (Fin.ext hMarkerColumn) hLower hInsideHeight
          have hFixed := d.stationary_child_for_active_parent hSource a hcm hParent hInside
            hChildColumn s.next_lower hAfter hNoBetween hUpper hStationary
          obtain ⟨index, cell, hBelow, hCell, hRow⟩ :=
            s.actual_active_parent history hLast a hInside hAbove hParent hChildColumn hUpper
          refine ⟨_, cell, ?_, hCell, rfl, ?_⟩
          · simpa only [hFixed.2] using hBelow
          · exact hRow.trans (copy.interval_row a hInside hRight).symm
        · have hTargetCap : md.targetCell.row < Row.bump md.current.row a.degree := by
            rw [← hTarget]
            exact a.target_below
          have hCap := le_of_not_gt hInsideHeight
          obtain ⟨ref, cell, hBelow, hCell, hColumn, hRow⟩ := s.below_inactive_parent
            history hLast hParent hChildColumn hUpper hRight hm hRead copy.read.marker_before
              copy.read.no_between hReference hTargetCap hCap
          have hCopyRow : copy.read.outputCell.row = F.height parent := by
            rw [copy.read.output_row]
            exact Row.lift_eq_of_ge_cap md.target_lower hTargetCap hCap
          exact ⟨ref, cell, hBelow, hCell, hColumn, hRow.trans hCopyRow.symm⟩
      · have hUnraised : md.targetCell.row = md.current.row :=
          le_antisymm (le_of_not_gt hRaised) md.target_lower
        have hIdentityReference : referenceAt start references md.current.row = .ok md.current.row := by
          simpa only [hUnraised] using hReference
        have hCap : Row.bump md.current.row 0 ≤ F.height parent := by
          by_contra hn
          have hj := Row.jump_le_of_lt_bump hAbove.le (lt_of_not_ge hn)
          have he := Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero hj)
          exact (ne_of_lt hAbove) he
        obtain ⟨ref, cell, hBelow, hCell, hColumn, hRow⟩ := s.below_inactive_parent
          history hLast hParent hChildColumn hUpper hRight hm hRead copy.read.marker_before
            copy.read.no_between hIdentityReference (Row.lt_bump _ 0) hCap
        have hCopyRow : copy.read.outputCell.row = F.height parent := by
          rw [copy.read.output_row]
          change Row.lift md.current.row md.targetCell.row (F.height parent) = _
          rw [hUnraised]
          exact Row.lift_identity hLower
        exact ⟨ref, cell, hBelow, hCell, hColumn, hRow.trans hCopyRow.symm⟩
  obtain ⟨ref, cell, hBelow, hReadCell, hColumn, hRow⟩ := hSelected
  have hRef : ref = copy.outputRef := ref_eq_of_same_column_row s.ambient_valid
    hReadCell copy.output_read (hColumn.trans copy.source_column.symm) hRow
  exact ⟨copy, hRef ▸ hBelow⟩

/-- The child occurrence is first constructed from the actual run. If
its row is stationary, the raw father is then constructed as the exact
effective occurrence of the source father. A marked source successor is
handled by its real marker-seam execution, without an adjacency premise. -/
theorem DynamicBlockState.actual_stationary_contour_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      (childCopy.read.outputCell.row = (Frame.ofMountain p.reduced).height child →
        ∃ parentCopy : EffectiveCopyOccurrence p block start references parent (ambient.push column),
          RawRefEdge (ambient.push column) childCopy.outputRef parentCopy.outputRef) := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead := d.frame_source_read hSource (rfl : child.1.val = child.1.val)
  have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
    have hRead := d.frame_source_read hSource (congrArg Fin.val (Frame.upper_spec hUpper).1)
    simpa only [(Frame.upper_spec hUpper).2] using hRead
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
  let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
    ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
  refine ⟨childCopy, rfl, rfl, ?_⟩
  intro hStationary
  change read.outputCell.row = F.height child at hStationary
  let md := d.marker_data read.marker read.marker_mem
  have hLiftChild : Row.lift md.current.row md.targetCell.row (F.height child) = F.height child :=
    read.output_row.symm.trans hStationary
  obtain ⟨oldParentCopy, hBelow⟩ := s.below_stationary_effective_parent history hLast d
    hParent rfl hRight hUpper read.marker_mem read.marker_before read.no_between hLiftChild
  have hChildReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldParent, hOldParent, hSourceB, _, hStored⟩ := hNormal.upper_step child sourceUpper hChildReal hUpper
  have hParentEq : oldParent = parent := Option.some.inj (hOldParent.symm.trans hParent)
  subst oldParent
  change (F.cell sourceUpper).left = some (Frame.ref parent) at hStored
  change F.height sourceUpper = Row.B (F.height child) (F.height parent) at hSourceB
  have hRootLower : md.current.row ≤ F.height child := read.source_lower
  have hUpperFixed : Row.lift md.current.row md.targetCell.row (F.height sourceUpper) =
      F.height sourceUpper := by
    rw [hSourceB, Row.B, Row.lift_bump hRootLower, hLiftChild]
  have hProduced : ∃ (upper copied : Cell), column[read.outputIndex + 1]? = some upper ∧
      copyEdge ambient ⟨child.1.val, child.2.val + 1⟩
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (F.height sourceUpper) = .ok copied ∧ SameShape copied upper := by
    by_cases hUpperMarked : child.2.val + 1 ∈ d.bucket.map Ref.index
    · obtain ⟨upper, copied, hUpperRead, _, hCopy, hShape⟩ :=
        d.effective_upper_marker_execution hParentPower hParentLow hNoPremature
          read hSourceUpper hUpperMarked
      exact ⟨upper, copied, hUpperRead, hCopy, hShape⟩
    · have hAfter : read.marker.index < child.2.val := by
        have hBefore := read.marker_before
        have hNe : read.marker.index ≠ child.2.val := by
          intro he
          exact hUnmarked (he ▸ List.mem_map.mpr ⟨read.marker, read.marker_mem, rfl⟩)
        omega
      have hNoBetween : ∀ middle, read.marker.index < middle → middle ≤ child.2.val + 1 →
          middle ∉ d.bucket.map Ref.index := by
        intro middle hLow hHigh
        by_cases hLe : middle ≤ child.2.val
        · exact read.no_between middle hLow hLe
        · have he : middle = child.2.val + 1 := by omega
          exact he ▸ hUpperMarked
      obtain ⟨position, lower, upper, copied, hLo, hHi, hLoRow, _, hCopy, hShape⟩ :=
        d.copyColumn_source_adjacent_execution hParentPower hParentLow hNoPremature hRun
          read.marker_mem hChildRead hSourceUpper hAfter hNoBetween
      obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
      have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
      subst actual
      have hIndex : position = read.outputIndex := column_read_index_eq_of_row
        hValid hLo read.output_at (hLoRow.trans read.output_row.symm)
      refine ⟨upper, copied, hIndex ▸ hHi, ?_, hShape⟩
      change copyEdge ambient ⟨child.1.val, child.2.val + 1⟩
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift md.current.row md.targetCell.row (F.height sourceUpper)) = .ok copied at hCopy
      simpa only [hUpperFixed] using hCopy
  obtain ⟨upper, copied, hHi, hCopy, hShape⟩ := hProduced
  have hLookup : lookup ambient ⟨child.1.val, child.2.val + 1⟩ = .ok (F.cell sourceUpper) :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, hSourceUpper⟩
  have hNonzero : (F.cell sourceUpper).row ≠ 0 := ne_of_gt
    (Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered (upper_real hUpper)))
  have hNotFixed : ¬ (Frame.ref parent).column < p.root.column := by
    change ¬ parent.1.val < p.root.column
    omega
  have hDestination : oldParentCopy.outputRef.column < child.1.val +
      block * (p.reduced.size - 1 - p.root.column) := by
    rw [oldParentCopy.source_column]
    exact Nat.add_lt_add_right (Frame.P_column_lt hNormal.toOrdered hParent) _
  change below ambient ((Frame.ref parent).column +
    block * (p.reduced.size - 1 - p.root.column)) (F.height sourceUpper) =
      .ok oldParentCopy.outputRef at hBelow
  have hCopied : (⟨F.height sourceUpper, 0, some oldParentCopy.outputRef⟩ : Cell) = copied := by
    simpa [copyEdge, hLookup, hNonzero, leftOf, hStored, hNotFixed,
      hBelow, Nat.not_le_of_gt hDestination] using hCopy
  have hCopiedLeft : copied.left = some oldParentCopy.outputRef := congrArg Cell.left hCopied.symm
  let parentCopy := oldParentCopy.extend (PreservesColumns.push ambient column)
  refine ⟨parentCopy, read.outputCell, upper, oldParentCopy.read.outputCell, read.output_read,
    ?_, hShape.2.symm.trans hCopiedLeft, parentCopy.output_read⟩
  exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
    EffectiveCopyRead.outputRef], by
      change column[read.outputIndex + 1]? = some upper
      exact hHi⟩

/-- The stationary result can use an independently chosen occurrence of
the same source. Actual execution coherence identifies its reference and
row with the constructed child, without a final Normal premise. -/
theorem DynamicBlockState.stationary_effective_parent_of_occurrence
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (hUnmarked : child.2.val ∉ (p.marked[child.1.val]?.getD []).map Ref.index)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
    (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
    (hStationary : childCopy.read.outputCell.row = (Frame.ofMountain p.reduced).height child) :
    ∃ parentCopy : EffectiveCopyOccurrence p block start references parent (ambient.push column),
      RawRefEdge (ambient.push column) childCopy.outputRef parentCopy.outputRef := by
  obtain ⟨actual, _, _, hConditional⟩ := s.actual_stationary_contour_effective_parent
    history hLast hParent hChildColumn hRight hUnmarked hRun
  obtain ⟨parentCopy, hEdge⟩ := hConditional ((actual.effective_row_unique childCopy).trans hStationary)
  exact ⟨parentCopy, (actual.unique childCopy).1 ▸ hEdge⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.below_stationary_effective_parent
#print axioms OmegaY.Expansion.DynamicBlockState.actual_stationary_contour_effective_parent
#print axioms OmegaY.Expansion.DynamicBlockState.stationary_effective_parent_of_occurrence
