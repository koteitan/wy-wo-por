/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ColumnEdgeSourceClassification.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.AdjacentEffectiveSources

/-! Exhaustive executable edge provenance for the key argument: an
ordinary edge has a real effective source lower and its consecutive
source upper; every other edge's upper is produced by an actual fill. -/

namespace OmegaY.Expansion
open Canonical

def FillUpperOrigin {mountain : Mountain} {marked : Array (List Ref)}
    {references : List Ref} {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (upper : Cell) : Prop :=
  ∃ (marker : Ref) (hm : marker ∈ d.bucket) (gap : List Cell) (original : Cell),
    fill mountain ⟨sourceColumn, marker.index + 1⟩ shift
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row = .ok gap ∧
    original ∈ gap ∧ SameShape original upper

namespace ColumnCopyData
variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

theorem fill_upper_origin_of_ascending {marker : Ref} (hm : marker ∈ d.bucket)
    {original upper : Cell}
    (hMem : original ∈ fillCellsAscending (d.marker_data marker hm).parentNodes
      ((d.marker_data marker hm).sourceParent.column + shift)
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row)
    (hShape : SameShape original upper) : FillUpperOrigin d upper := by
  let md := d.marker_data marker hm
  obtain ⟨hp, hParentEq⟩ := Array.getElem?_eq_some_iff.mp md.parent_nodes
  have hParentValid : ColumnValid mountain (md.sourceParent.column + shift) md.parentNodes :=
    hParentEq ▸ d.ambient_valid _ hp
  have hRead : lookup mountain ⟨sourceColumn, marker.index + 1⟩ = .ok md.upper :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, md.upper_at⟩
  have hLeft := (d.source_valid.stored_valid _ _ _ md.upper_at md.upper_left).1
  have hFill := fill_eq_cells hRead md.upper_left md.parent_nodes
    (fillRowsStrict_of_columnValid hParentValid) md.target_at le_rfl
    (Nat.add_lt_add_right hLeft shift) (low := md.current.row)
  exact ⟨marker, hm, _, original, hFill, (fillCellsAscending_perm _ _ _ _).mem_iff.mp hMem, hShape⟩

/-- Every actual adjacent output pair is classified. No source node,
marker interval, parent, or target key comparison is supplied by the caller. -/
theorem adjacent_effective_or_fill
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[i]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {index : Nat} {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper) :
    Nonempty (EffectiveAdjacentSource d column index lower) ∨ FillUpperOrigin d upper := by
  have hOrigin := d.copyColumn_adjacent_origin hParentPower hParentLow hNoPremature hRun hLower hUpper
  cases hOrigin with
  | inside before marker after localIndex originalLower originalUpper hm hSplit hPosition hLow hUp hLowShape hUpShape =>
    obtain ⟨copied, path, hCopy, hContour, hSegment⟩ :=
      d.sorted_segment_adjacent_origin hParentPower hParentLow hm hLow hUp
    let pair : ExecutedSegmentPair d index lower upper := {
      marker := marker, member := hm, before := before, after := after,
      localIndex := localIndex, originalLower := originalLower, originalUpper := originalUpper,
      copied := copied, path := path, bucket_split := hSplit, position := hPosition,
      lower_sorted := hLow, upper_sorted := hUp, lower_shape := hLowShape,
      upper_shape := hUpShape, copy_run := hCopy, contour_run := hContour }
    cases hSegment with
    | marker_fill _ _ hHead =>
      exact Or.inr (d.fill_upper_origin_of_ascending hm (List.mem_of_head? hHead) hUpShape)
    | marker_contour _ hEq hEmpty _ =>
      exact Or.inl (pair.marker_contour_effective_source hRun hLower hParentLow hEq hEmpty)
    | fill_inside _ _ _ hFillUp =>
      exact Or.inr (d.fill_upper_origin_of_ascending hm (List.mem_of_getElem? hFillUp) hUpShape)
    | fill_contour _ _ hFillLast _ =>
      exact Or.inl (pair.fill_contour_effective_source hRun hLower hParentPower hParentLow hFillLast)
    | contour_inside _ _ hPathLow hPathUp =>
      exact Or.inl (pair.contour_effective_source hRun hLower hPathLow hPathUp)
  | seam before lowMarker highMarker after originalLower originalUpper hLowMember hHighMember
      hSplit hOrder hNoBetween hPosition hLow hUp hLowShape hUpShape =>
    let seam : ExecutedSegmentSeam d index lower upper := {
      lowMarker := lowMarker, highMarker := highMarker,
      low_member := hLowMember, high_member := hHighMember,
      before := before, after := after, originalLower := originalLower, originalUpper := originalUpper,
      bucket_split := hSplit, marker_order := hOrder, no_between := hNoBetween,
      position := hPosition, lower_last := hLow, upper_head := hUp,
      lower_shape := hLowShape, upper_shape := hUpShape }
    exact Or.inl (seam.effective_source hParentPower hParentLow hNoPremature hRun hLower)

end ColumnCopyData
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.fill_upper_origin_of_ascending
#print axioms OmegaY.Expansion.ColumnCopyData.adjacent_effective_or_fill
