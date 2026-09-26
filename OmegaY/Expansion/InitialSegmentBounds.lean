/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialSegmentBounds.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialSegmentData
import OmegaY.Expansion.SegmentBounds

/-!
# Ranges of segments from actual initial preparation

All local segment inputs and the interval separating two actual markers are
derived from Preparation. The caller supplies only actual reads and actual
successful segment outputs, not a chosen target or a separation invariant.
-/

namespace OmegaY.Expansion

open Canonical

/-- Arbitrary successful initial segment output contains its marker row and
has no row below it. Its rows are internally distinct. -/
theorem Preparation.initial_segment_result_bounds {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {sources : Column} (hSources : p.reduced[p.root.column + 1]? = some sources)
    {marker : Ref} (hMarker : BucketMem p.marked (p.root.column + 1) marker)
    {current : Cell} (hCurrent : Canonical.cellAt p.reduced marker = .ok current)
    {result : List Cell}
    (hRun : copySegment p.reduced sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result) :
    (result.map Cell.row).Nodup ∧ current.row ∈ result.map Cell.row ∧
      ∀ cell ∈ result, current.row ≤ cell.row := by
  obtain ⟨d⟩ := p.first_segment_data hLast hMap hMarker
  have hSourcesEq : d.sources = sources :=
    Option.some.inj (d.source_column.symm.trans hSources)
  have hCurrentEq : d.current = current :=
    Except.ok.inj (d.current_read.symm.trans hCurrent)
  have hRunD : copySegment p.reduced d.sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result := by
    simpa only [hSourcesEq] using hRun
  have hBounds := copySegment_result_bounds p.reduced_valid d.source_column (by omega)
    d.destination d.source_top references ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
    d.current_at d.upper_at d.upper_left d.parent_nodes d.target_at d.reference d.target_lower hRunD
  simpa only [hCurrentEq] using hBounds

/-- Every row copied from a lower actual marker is strictly below a higher
actual marker. The target's power cap comes from the root-reference theorem,
and the actual source power steps come from the successful reduced build. -/
theorem Preparation.initial_segment_result_lt_marker {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {sources : Column} (hSources : p.reduced[p.root.column + 1]? = some sources)
    {marker : Ref} (hMarker : BucketMem p.marked (p.root.column + 1) marker)
    {result : List Cell}
    (hRun : copySegment p.reduced sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result)
    {nextMarker : Ref} (hNextMarker : BucketMem p.marked (p.root.column + 1) nextMarker)
    {nextCell : Cell} (hNext : Canonical.cellAt p.reduced nextMarker = .ok nextCell)
    (hIndex : marker.index < nextMarker.index) :
    ∀ cell ∈ result, cell.row < nextCell.row := by
  obtain ⟨d⟩ := p.first_segment_data hLast hMap hMarker
  have hSourcesEq : d.sources = sources :=
    Option.some.inj (d.source_column.symm.trans hSources)
  have hRunD : copySegment p.reduced d.sources references (p.root.column + 1)
      ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
      (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok result := by
    simpa only [hSourcesEq] using hRun
  have hNextColumn : nextMarker.column = p.root.column + 1 := (p.marker_iff.mp hNextMarker).1
  obtain ⟨nextSources, hNextSources, hNextIndex⟩ := cellAt_ok_iff.mp hNext
  have hNextSources' : p.reduced[p.root.column + 1]? = some nextSources := by
    simpa only [hNextColumn] using hNextSources
  have hNextSourcesEq : nextSources = d.sources :=
    Option.some.inj (hNextSources'.symm.trans d.source_column)
  have hNextAt : d.sources[nextMarker.index]? = some nextCell := by
    simpa only [hNextSourcesEq] using hNextIndex
  have hStrict : d.current.row < nextCell.row :=
    d.source_valid.rows_strict _ _ _ _ d.current_at hNextAt hIndex
  obtain ⟨target, ceiling, degree, hReference, _, hTargetUpper, hCeiling, hCap⟩ :=
    p.initial_marker_reference_below hLast hMap hMarker d.current_read hNextMarker hNext hStrict
  have hTargetEq : target = d.targetCell.row :=
    Except.ok.inj (hReference.symm.trans d.reference)
  have hUpper : d.targetCell.row < Row.bump d.current.row degree := by
    simpa only [hTargetEq, hCeiling] using hTargetUpper
  have hCap' : Row.bump d.current.row degree ≤ nextCell.row := by
    simpa only [hCeiling] using hCap
  have hMarked : nextMarker.index ∈ (p.marked[p.root.column + 1]?.getD []).map Ref.index :=
    List.mem_map.mpr ⟨nextMarker, hNextMarker, rfl⟩
  exact copySegment_result_lt_next_marker p.reduced_valid d.source_column (by omega)
    d.destination d.source_top references ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
    d.current_at d.upper_at d.upper_left d.parent_nodes d.target_at d.reference d.target_lower hRunD
    (build_column_power_steps_of_read p.reduced_build d.source_column) hNextAt hMarked hIndex hUpper hCap'

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_segment_result_bounds
#print axioms OmegaY.Expansion.Preparation.initial_segment_result_lt_marker
