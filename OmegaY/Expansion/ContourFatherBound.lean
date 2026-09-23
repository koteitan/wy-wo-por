/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourFatherBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.SourceFatherBound
import OmegaY.Expansion.ActualMarkerTransport
import OmegaY.Expansion.ActualRemainingRaw

/-!
# Actual contour cells respect their stored father's upper row

For fixed source parents, the actual marker classification proves that
the requested upper row is unchanged. For moved parents, strict-below
maximality supplies the bound directly. The phantom-start case uses the
actual reference-at-zero rule. No unchanged-query or output numerical
parent hypothesis is supplied by the caller.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A source edge with a father left of the bad root has an unchanged
upper row under its actual controlling marker's lift. The child itself
may lie inside a genuinely raised interval. -/
theorem DynamicBlockState.fixed_parent_marker_lift_upper
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hAfter : marker.index ≤ child.2.val)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hFixed : parent.1.val < p.root.column) :
    Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row
      ((Frame.ofMountain p.reduced).height upper) = (Frame.ofMountain p.reduced).height upper := by
  let F := Frame.ofMountain p.reduced
  let md := d.marker_data marker hm
  have hNormal := build_normal_of_success p.reduced_build
  have hNext : next < p.reduced.size := by
    have h := child.1.isLt
    simpa only [Frame.ofMountain, hChildColumn] using h
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hRootLower : md.current.row ≤ F.height child :=
    d.marker_source_row_le hm (d.frame_source_read hSource hChildColumn) hAfter
  have hSourceB : F.height upper = Row.B (F.height child) (F.height parent) :=
    (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
  have hOfFixedLower : Row.lift md.current.row md.targetCell.row (F.height child) = F.height child →
      Row.lift md.current.row md.targetCell.row (F.height upper) = F.height upper := by
    intro hLowerFixed
    rw [hSourceB, Row.B, Row.lift_bump hRootLower, hLowerFixed]
  rcases s.marker_source_transport hLast d hm hChildColumn hAfter with
    ⟨_, hLowerFixed⟩ | ⟨rootIndex, a, hTarget, hRaised, hClassification⟩
  · exact hOfFixedLower hLowerFixed
  · rcases hClassification with hInside | ⟨_, hLowerFixed⟩
    · have hExecutable := (Executable.findParent_ref_iff hNormal.toOrdered child parent).mpr hParent
      have hCopy := (s.copyEdge_fixed_interval_parent a hRaised hExecutable hInside hUpper hFixed).1
      have hRow := copyEdge_return_row hCopy
      simpa only [hTarget] using hRow.symm
    · exact hOfFixedLower hLowerFixed

/-- Every indexed cell of the actual contour copy has the upper bound at
its stored father's actual successor. Source adjacency, marker control,
and the copied edge are read from the execution packet. -/
theorem DynamicBlockState.contourNth_father_bound
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    (hSource : p.reduced[next]? = some d.sources)
    {marker : Ref} (hm : marker ∈ d.bucket) {path : List Cell} {position : Nat} {copied : Cell}
    (execution : ContourNthExecution ambient next (d.bucket.map Ref.index)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column d.sources
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row
      marker.index path position copied) :
    CellRawFatherBound ambient copied := by
  let md := d.marker_data marker hm
  have hUpperRead : Canonical.cellAt p.reduced ⟨next, marker.index + position + 1⟩ =
      .ok execution.upper := cellAt_ok_iff.mpr ⟨d.sources, hSource, execution.upper_at⟩
  have hAtSourceRow : Row.lift md.current.row md.targetCell.row execution.upper.row = execution.upper.row →
      CellRawFatherBound ambient copied := by
    intro hFixedQuery
    have hCopy := execution.copy_run
    change copyEdge ambient ⟨next, marker.index + position + 1⟩
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift md.current.row md.targetCell.row execution.upper.row) = .ok copied at hCopy
    rw [hFixedQuery] at hCopy
    exact s.copyEdge_source_row_father_bound hUpperRead hCopy
  by_cases hZero : execution.lower.row = 0
  · have hRootZero : md.current.row = 0 := le_antisymm
      (by simpa only [hZero] using execution.root_lower) (Row.zero_le _)
    have hTargetZero : md.targetCell.row = 0 := d.target_zero hm hRootZero
    apply hAtSourceRow
    have hIdentity : ∀ row : Row, Row.lift md.current.row md.targetCell.row row = row := by
      intro row
      rw [hRootZero, hTargetZero]
      exact Row.lift_identity (Row.zero_le _)
    exact hIdentity execution.upper.row
  · obtain ⟨source⟩ := source_numerical_pair_of_reads (build_normal_of_success p.reduced_build)
      hSource execution.lower_at execution.upper_at hZero
    by_cases hFixed : source.parentNode.1.val < p.root.column
    · have hChildColumn : source.lowerNode.1.val = next := congrArg Ref.column source.lower_ref
      have hAfter : marker.index ≤ source.lowerNode.2.val := by
        have hIndex := congrArg Ref.index source.lower_ref
        change source.lowerNode.2.val = marker.index + position at hIndex
        omega
      have hFixedQuery := s.fixed_parent_marker_lift_upper hLast d hm source.source_parent
        hChildColumn hAfter source.source_upper hFixed
      apply hAtSourceRow
      simpa only [Frame.height, source.upper_cell] using hFixedQuery
    · have hLookup : lookup ambient ⟨next, marker.index + position + 1⟩ = .ok execution.upper :=
        lookup_ok_iff.mpr (cellAt_ok_iff.mp (p.cell_read_preserved s.base_ambient hUpperRead))
      exact copyEdge_moved_rawFatherBound execution.copy_run hLookup source.upper_left
        (Nat.le_of_not_gt hFixed)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.fixed_parent_marker_lift_upper
#print axioms OmegaY.Expansion.DynamicBlockState.contourNth_father_bound
