/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SecondSegmentControls.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.SecondSegments
import OmegaY.Expansion.PreparedExtension
import OmegaY.Expansion.SegmentPositive

/-! Positive parents and cross-marker bounds for the actual second-column
segments. These are derived in the extended ambient mountain; the first
copied column is not assumed canonical or to have adjacent power steps. -/

namespace OmegaY.Expansion

open Canonical

theorem SecondSegmentData.source_valid {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {firstColumn : Column} {marker : Ref}
    (d : SecondSegmentData p references firstColumn marker) :
    ColumnValid (p.reduced.push firstColumn) (p.root.column + 2) d.sources := by
  obtain ⟨hc, hSources⟩ := Array.getElem?_eq_some_iff.mp d.source_column
  exact hSources ▸ d.ambient_valid _ hc

theorem SecondSegmentData.ambient_current_read {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {firstColumn : Column} {marker : Ref}
    (d : SecondSegmentData p references firstColumn marker) :
    Canonical.cellAt (p.reduced.push firstColumn) marker = .ok d.current :=
  cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_column] using d.source_column, d.current_at⟩

theorem SecondSegmentData.target_zero {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {firstColumn : Column} {marker : Ref}
    (d : SecondSegmentData p references firstColumn marker) (hLast : 1 < last)
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    (hZero : d.current.row = 0) : d.targetCell.row = 0 := by
  have hReference := d.base_reference
  rw [hZero] at hReference
  exact Except.ok.inj (hReference.symm.trans (p.initial_referenceAt_zero hLast hMap))

section Segment

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {references : List Ref} {firstColumn : Column} {marker : Ref}
  (d : SecondSegmentData p references firstColumn marker)
  (hLast : 1 < last)
  (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
  {result : List Cell}
  (hRun : copySegment (p.reduced.push firstColumn) d.sources references (p.root.column + 2)
    ((p.marked[p.root.column + 2]?.getD []).map Ref.index)
    (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result)

include hRun

theorem SecondSegmentData.result_bounds :
    (result.map Cell.row).Nodup ∧ d.current.row ∈ result.map Cell.row ∧
      ∀ cell ∈ result, d.current.row ≤ cell.row :=
  copySegment_result_bounds d.ambient_valid d.source_column (by omega) d.destination d.source_top
    references _ d.current_at d.upper_at d.upper_left d.parent_nodes d.target_at
    d.reference d.target_lower hRun

include hLast hMap

theorem SecondSegmentData.result_positive :
    ∀ cell ∈ result, (1 : Row) < cell.row →
      ∃ parent parentCell, cell.left = some parent ∧
        lookup (p.reduced.push firstColumn) parent = .ok parentCell ∧ 0 < parentCell.value :=
  copySegment_positive_of_source d.ambient_valid d.source_column (by omega) d.destination
    d.source_top d.source_power d.source_positive references _ d.current_at d.upper_at
    d.upper_left d.parent_nodes d.target_at d.reference d.target_lower
    (d.target_zero hLast hMap) hRun

/-- A whole lower segment is strictly below any higher actual marker in
this source column, despite its contour lifting and reference filling. -/
theorem SecondSegmentData.result_lt_marker
    (hMarker : BucketMem p.marked (p.root.column + 2) marker)
    {nextMarker : Ref} {nextCell : Cell}
    (hNextMarker : BucketMem p.marked (p.root.column + 2) nextMarker)
    (hNext : d.sources[nextMarker.index]? = some nextCell)
    (hIndex : marker.index < nextMarker.index) :
    ∀ cell ∈ result, cell.row < nextCell.row := by
  have hNextColumn := (p.marker_iff.mp hNextMarker).1
  have hNextRead : Canonical.cellAt (p.reduced.push firstColumn) nextMarker = .ok nextCell :=
    cellAt_ok_iff.mpr ⟨d.sources, by simpa only [hNextColumn] using d.source_column, hNext⟩
  have hStrict := d.source_valid.rows_strict marker.index nextMarker.index d.current nextCell
    d.current_at hNext hIndex
  obtain ⟨target, ceiling, degree, hReference, _, hHigh, hPower, hCap⟩ :=
    p.initial_marker_reference_below_extended hLast (PreservesColumns.push p.reduced firstColumn)
      hMap hMarker d.ambient_current_read hNextMarker hNextRead hStrict
  have hTargetEq : target = d.targetCell.row := Except.ok.inj (hReference.symm.trans d.reference)
  have hTargetUpper : d.targetCell.row < Row.bump d.current.row degree := by
    simpa only [hTargetEq, hPower] using hHigh
  have hCeiling : Row.bump d.current.row degree ≤ nextCell.row := by
    simpa only [hPower] using hCap
  exact copySegment_result_lt_next_marker d.ambient_valid d.source_column (by omega)
    d.destination d.source_top references _ d.current_at d.upper_at d.upper_left
    d.parent_nodes d.target_at d.reference d.target_lower hRun d.source_power hNext
    (List.mem_map.mpr ⟨nextMarker, hNextMarker, rfl⟩) hIndex hTargetUpper hCeiling

end Segment

end OmegaY.Expansion

#print axioms OmegaY.Expansion.SecondSegmentData.result_positive
#print axioms OmegaY.Expansion.SecondSegmentData.result_lt_marker
