/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRemainingRaw.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRawCases
import OmegaY.Expansion.RaisedSeamGeometry
import OmegaY.Expansion.StationarySeamGeometry
import OmegaY.Expansion.StationaryContourGeometry

/-!
# Exact remaining stationary moved-parent cases

This classification removes all previously solved fill, marker, raised,
and fixed-parent-column cases from real output adjacency. Each remaining
case carries consecutive source reads and its actual source numerical
father. Neither output Normal nor the desired raw B equation is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A source pair with its actual numerical father. Its cell fields refer
to the frozen source mountain, before copying or numerical backfill. -/
structure SourceNumericalPair (mountain : Mountain) (column index : Nat) (lower upper : Cell) where
  lowerNode : (Frame.ofMountain mountain).Node
  parentNode : (Frame.ofMountain mountain).Node
  upperNode : (Frame.ofMountain mountain).Node
  lower_ref : Frame.ref lowerNode = ⟨column, index⟩
  upper_ref : Frame.ref upperNode = ⟨column, index + 1⟩
  lower_cell : (Frame.ofMountain mountain).cell lowerNode = lower
  upper_cell : (Frame.ofMountain mountain).cell upperNode = upper
  lower_real : Frame.Real lowerNode
  source_upper : (Frame.ofMountain mountain).upper lowerNode = some upperNode
  source_parent : (Frame.ofMountain mountain).P lowerNode = some parentNode
  upper_left : upper.left = some (Frame.ref parentNode)
  upper_row : upper.row = Row.B lower.row ((Frame.ofMountain mountain).height parentNode)
  parent_read : Canonical.cellAt mountain (Frame.ref parentNode) =
    .ok ((Frame.ofMountain mountain).cell parentNode)
  parent_lower : (Frame.ofMountain mountain).height parentNode ≤ lower.row

private theorem upper_of_actual_refs {F : Frame} {before after : F.Node} {column index : Nat}
    (hBefore : Frame.ref before = ⟨column, index⟩)
    (hAfter : Frame.ref after = ⟨column, index + 1⟩) : F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hBefore hAfter
  have hc : d = c := Fin.ext (hAfter.1.trans hBefore.1.symm)
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, by omega⟩

/-- Source Normal, actual consecutive reads, and a nonzero lower row
construct the certificate. Source P and stored-left identities are outputs. -/
theorem source_numerical_pair_of_reads {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal) {column index : Nat} {nodes : Column}
    (hColumn : mountain[column]? = some nodes) {lower upper : Cell}
    (hLower : nodes[index]? = some lower) (hUpper : nodes[index + 1]? = some upper)
    (hNonzero : lower.row ≠ 0) : Nonempty (SourceNumericalPair mountain column index lower upper) := by
  have hLowerRead : Canonical.cellAt mountain ⟨column, index⟩ = .ok lower :=
    cellAt_ok_iff.mpr ⟨nodes, hColumn, hLower⟩
  have hUpperRead : Canonical.cellAt mountain ⟨column, index + 1⟩ = .ok upper :=
    cellAt_ok_iff.mpr ⟨nodes, hColumn, hUpper⟩
  obtain ⟨child, hChildRef, hChildCell⟩ := Canonical.frame_node_of_cellAt hLowerRead
  obtain ⟨above, hAboveRef, hAboveCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hReal : Frame.Real child := by
    by_contra hn
    have hi : child.2.val = 0 := by unfold Frame.Real at hn; omega
    have hFin : child.2 = ⟨0, by have := child.2.isLt; omega⟩ := Fin.ext hi
    have hZero : (Frame.ofMountain mountain).height child = 0 := by
      change ((Frame.ofMountain mountain).cells child.1 child.2).row = 0
      rw [hFin, hNormal.phantom]
      rfl
    exact hNonzero (by simpa only [Frame.height, hChildCell] using hZero)
  have hAdjacent : (Frame.ofMountain mountain).upper child = some above :=
    upper_of_actual_refs hChildRef hAboveRef
  obtain ⟨parent, hParent, hRow, _, hStored⟩ := hNormal.upper_step child above hReal hAdjacent
  exact ⟨{
    lowerNode := child
    parentNode := parent
    upperNode := above
    lower_ref := hChildRef
    upper_ref := hAboveRef
    lower_cell := hChildCell
    upper_cell := hAboveCell
    lower_real := hReal
    source_upper := hAdjacent
    source_parent := hParent
    upper_left := by simpa only [hAboveCell] using hStored
    upper_row := by simpa only [Frame.height, hChildCell, hAboveCell] using hRow
    parent_read := cellAt_of_frame_node mountain parent
    parent_lower := by simpa only [Frame.height, hChildCell] using Frame.P_height_le hNormal.toOrdered hParent }⟩

/-- The only unresolved origins are stationary contour interiors and
stationary joins, with source fathers in columns that the program moves.
Both actual output rows equal their respective source rows. -/
inductive RemainingMovedStationaryOrigin {front : List Nat} {last : Nat}
    (p : Preparation front last) {mountain : Mountain} {references : List Ref}
    {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (index : Nat) (lower upper : Cell) : Prop where
  | contour_inside (pair : ExecutedSegmentPair d index lower upper) (pathIndex : Nat)
      (position : pair.localIndex = 1 + pair.fill.length + pathIndex)
      (lower_read : pair.path[pathIndex]? = some pair.originalLower)
      (upper_read : pair.path[pathIndex + 1]? = some pair.originalUpper)
      (execution : ContourAdjacentExecution mountain sourceColumn (d.bucket.map Ref.index)
        shift p.root.column d.sources (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row pair.marker.index pair.path
        pathIndex pair.originalLower pair.originalUpper)
      (source : SourceNumericalPair p.reduced sourceColumn (pair.marker.index + pathIndex + 1)
        execution.lower execution.upper)
      (lower_stationary : execution.lower.row = lower.row)
      (upper_stationary : execution.upper.row = upper.row)
      (parent_moved : p.root.column ≤ source.parentNode.1.val)
      (upper_copy : copyEdge mountain (Frame.ref source.upperNode) shift p.root.column
        execution.upper.row = .ok pair.originalUpper) :
      RemainingMovedStationaryOrigin p d index lower upper
  | cross_segment (seam : ExecutedSegmentSeam d index lower upper) (sourceLower : Cell)
      (source_read : d.sources[seam.highMarker.index - 1]? = some sourceLower)
      (lower_lift : lower.row = Row.lift (d.marker_data seam.lowMarker seam.low_member).current.row
        (d.marker_data seam.lowMarker seam.low_member).targetCell.row sourceLower.row)
      (source : SourceNumericalPair p.reduced sourceColumn (seam.highMarker.index - 1)
        sourceLower (d.marker_data seam.highMarker seam.high_member).current)
      (lower_stationary : sourceLower.row = lower.row)
      (upper_stationary : (d.marker_data seam.highMarker seam.high_member).current.row = upper.row)
      (parent_moved : p.root.column ≤ source.parentNode.1.val)
      (upper_copy : copyEdge mountain (Frame.ref source.upperNode) shift p.root.column
        (d.marker_data seam.highMarker seam.high_member).current.row = .ok seam.originalUpper) :
      RemainingMovedStationaryOrigin p d index lower upper

/-- Complete refinement for a real current-column output. The copy-data
packet and all its power/support facts are constructed from the dynamic
state. The two residual constructors are conclusions of actual execution. -/
theorem DynamicBlockState.actual_adjacent_remaining_raw_cases
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hNext : next < p.reduced.size) {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
    {index : Nat} {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hReal : lower.row ≠ 0) :
    CopiedRawAt ambient column lower upper ∨
      ∃ d : ColumnCopyData ambient p.marked references next
          (block * (p.reduced.size - 1 - p.root.column)) p.root.column,
        p.reduced[next]? = some d.sources ∧ NoPrematureOne d.sources ∧
        (∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes) ∧
        (∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
          (d.marker_data marker hm).parentNodes[i]? = some cell ∧
            cell.row = (d.marker_data marker hm).current.row) ∧
        RemainingMovedStationaryOrigin p d index lower upper := by
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast hNext
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hNormal := build_normal_of_success p.reduced_build
  rcases d.prepared_adjacent_raw_cases hSource hParentPower hParentLow hNoPremature
      hRun hLower hUpper hReal with hRaw | hOrigin
  · exact Or.inl hRaw
  cases hOrigin with
  | contour_inside pair pathIndex hPosition hLow hUp =>
    obtain ⟨execution, hLowerRow, hUpperRow, hRaised⟩ :=
      s.raised_contour_inside_geometry history hLast d pair hRun hLower hUpper hLow hUp
    by_cases hRise : execution.lower.row < lower.row
    · exact Or.inl ((hRaised hRise).raw_geometry)
    have hStationary : execution.lower.row = lower.row := by
      apply le_antisymm
      · rw [hLowerRow]
        exact Row.lift_ge_source (d.marker_data pair.marker pair.member).target_lower execution.root_lower
      · exact le_of_not_gt hRise
    obtain ⟨source⟩ := source_numerical_pair_of_reads hNormal hSource execution.lower_at
      (by simpa only [Nat.add_assoc] using execution.upper_at) (hStationary ▸ hReal)
    by_cases hFixed : (Frame.ref source.parentNode).column < p.root.column
    · exact Or.inl ((s.stationary_contour_fixed_geometry d pair execution hRun hLower hUpper
        hStationary source.upper_left hFixed).raw_geometry)
    have hLowerFixed : Row.lift (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row execution.lower.row = execution.lower.row :=
      hLowerRow.symm.trans hStationary.symm
    have hUpperFixed : Row.lift (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row execution.upper.row = execution.upper.row := by
      rw [source.upper_row, Row.B, Row.lift_bump execution.root_lower, hLowerFixed]
    have hCopied : copyEdge ambient (Frame.ref source.upperNode)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        execution.upper.row = .ok pair.originalUpper := by
      rw [source.upper_ref]
      simpa only [Nat.add_assoc, hUpperFixed] using execution.upper_copy
    exact Or.inr ⟨d, hSource, hNoPremature, hParentPower, hParentLow,
      .contour_inside pair pathIndex hPosition hLow hUp execution source hStationary
        (hUpperRow.trans hUpperFixed).symm (Nat.le_of_not_gt hFixed) hCopied⟩
  | cross_segment seam =>
    obtain ⟨sourceLower, hRead, hSourceUpper, hLowerRow, hUpperRow⟩ :=
      seam.source_predecessor hParentPower hParentLow hNoPremature
    by_cases hRise : sourceLower.row < lower.row
    · exact Or.inl ((s.raised_seam_source_geometry history hLast d seam hParentPower hParentLow
        hRun hLower hUpper hRead hLowerRow hRise).raw_geometry)
    have hStationary : sourceLower.row = lower.row := by
      apply le_antisymm
      · rw [hLowerRow]
        exact Row.lift_ge_source (d.marker_data seam.lowMarker seam.low_member).target_lower
          (d.marker_source_row_le seam.low_member hRead (by have := seam.marker_order; omega))
      · exact le_of_not_gt hRise
    obtain ⟨source⟩ := source_numerical_pair_of_reads hNormal hSource hRead hSourceUpper (hStationary ▸ hReal)
    by_cases hFixed : (Frame.ref source.parentNode).column < p.root.column
    · exact Or.inl ((s.stationary_seam_source_geometry d seam hParentPower hParentLow
        hRun hLower hUpper hRead hLowerRow hStationary hReal source.upper_left hFixed).raw_geometry)
    have hCopied : copyEdge ambient (Frame.ref source.upperNode)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (d.marker_data seam.highMarker seam.high_member).current.row = .ok seam.originalUpper := by
      rw [source.upper_ref]
      simpa only [show seam.highMarker.index - 1 + 1 = seam.highMarker.index by
        have := seam.marker_order; omega] using (seam.upper_copy hParentPower hParentLow).1
    exact Or.inr ⟨d, hSource, hNoPremature, hParentPower, hParentLow,
      .cross_segment seam sourceLower hRead hLowerRow source hStationary hUpperRow.symm
        (Nat.le_of_not_gt hFixed) hCopied⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.source_numerical_pair_of_reads
#print axioms OmegaY.Expansion.DynamicBlockState.actual_adjacent_remaining_raw_cases
