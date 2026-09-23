/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRawCases.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawRowCases
import OmegaY.Expansion.RaisedContourGeometry

/-! Exhaustive remaining raw-geometry cases for an actual column in any
copied block. Source/parent power and support premises are supplied by the
real dynamic state. Raised contour interiors have been discharged. -/

namespace OmegaY.Expansion

open Canonical

theorem ReturnedContourEdge.raw_geometry {ambient : Mountain} {column : Column}
    {index : Nat} {lower upper : Cell}
    (h : ReturnedContourEdge ambient column index lower upper) :
    CopiedRawAt ambient column lower upper := by
  obtain ⟨parentRef, parent, _, _, hLeft, hCol, hRead, hLow, hB⟩ := h
  exact ⟨parentRef, parent, hLeft, hRead, hCol, hLow, hB⟩

/-- The remaining contour case contains a real execution certificate
whose source lower row equals the output lower row. It must not be read
as saying that its parent's row is unchanged. -/
inductive RemainingStationaryRawOrigin {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (index : Nat) (lower upper : Cell) : Prop where
  | contour_inside (pair : ExecutedSegmentPair d index lower upper) (pathIndex : Nat)
      (position : pair.localIndex = 1 + pair.fill.length + pathIndex)
      (lower_read : pair.path[pathIndex]? = some pair.originalLower)
      (upper_read : pair.path[pathIndex + 1]? = some pair.originalUpper)
      (execution : ContourAdjacentExecution mountain sourceColumn (d.bucket.map Ref.index)
        shift rootColumn d.sources (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row pair.marker.index pair.path
        pathIndex pair.originalLower pair.originalUpper)
      (lower_stationary : execution.lower.row = lower.row)
      (upper_row : upper.row = Row.lift (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row execution.upper.row) :
      RemainingStationaryRawOrigin d index lower upper
  | cross_segment (seam : ExecutedSegmentSeam d index lower upper) :
      RemainingStationaryRawOrigin d index lower upper

/-- Every actual nonphantom output edge is either already proved to have
the required raw row geometry, an unraised contour interior, or a join
between actual consecutive segments. No copy-data packet is assumed. -/
theorem DynamicBlockState.actual_adjacent_raw_cases
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
        p.reduced[next]? = some d.sources ∧ RemainingStationaryRawOrigin d index lower upper := by
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast hNext
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  rcases d.prepared_adjacent_raw_cases hSource hParentPower hParentLow hNoPremature
      hRun hLower hUpper hReal with hRaw | hOrigin
  · exact Or.inl hRaw
  cases hOrigin with
  | contour_inside pair pathIndex hPosition hLow hUp =>
    obtain ⟨execution, hLowerRow, hUpperRow, hRaised⟩ :=
      s.raised_contour_inside_geometry history hLast d pair hRun hLower hUpper hLow hUp
    by_cases hRise : execution.lower.row < lower.row
    · exact Or.inl ((hRaised hRise).raw_geometry)
    · have hStationary : execution.lower.row = lower.row := by
        apply le_antisymm
        · rw [hLowerRow]
          exact Row.lift_ge_source (d.marker_data pair.marker pair.member).target_lower execution.root_lower
        · exact le_of_not_gt hRise
      exact Or.inr ⟨d, hSource, .contour_inside pair pathIndex hPosition hLow hUp execution
        hStationary hUpperRow⟩
  | cross_segment seam => exact Or.inr ⟨d, hSource, .cross_segment seam⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ReturnedContourEdge.raw_geometry
#print axioms OmegaY.Expansion.DynamicBlockState.actual_adjacent_raw_cases
