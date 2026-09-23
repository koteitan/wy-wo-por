/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreparedColumnData.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ColumnCopyData
import OmegaY.Expansion.InitialEndpoints

/-!
# Preparation supplies the generic input data for the first copied column

The data fields are actual source and parent-column reads plus selected
reference bounds. No segment success, candidate invariant, finished output,
or copied-column normality is used to populate the generic certificate.
The parent columns also have actual low-row reads and power steps, allowing
the entire fill-path theorem to be applied without new input assumptions.
-/

namespace OmegaY.Expansion

open Canonical

def FirstSegmentData.toMarkerCopyData {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {marker : Ref}
    (d : FirstSegmentData p references marker) {sources : Column}
    (hSources : p.reduced[p.root.column + 1]? = some sources) :
    MarkerCopyData p.reduced sources references
      (p.reduced.size - 1 - p.root.column) marker.index := by
  have he : d.sources = sources := Option.some.inj (d.source_column.symm.trans hSources)
  exact {
    current := d.current
    upper := d.upper
    sourceParent := d.sourceParent
    parentNodes := d.parentNodes
    targetIndex := d.targetIndex
    targetCell := d.targetCell
    current_at := by simpa only [he] using d.current_at
    upper_at := by simpa only [he] using d.upper_at
    upper_left := d.upper_left
    parent_nodes := d.parent_nodes
    target_at := d.target_at
    reference := d.reference
    target_lower := d.target_lower }

theorem FirstSegmentData.reference_cap {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {lower higher : Ref}
    (lo : FirstSegmentData p references lower) (hi : FirstSegmentData p references higher)
    (hLast : 1 < last)
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    (hLower : BucketMem p.marked (p.root.column + 1) lower)
    (hHigher : BucketMem p.marked (p.root.column + 1) higher)
    (hIndex : lower.index < higher.index) :
    ∃ scale, lo.targetCell.row < Row.bump lo.current.row scale ∧
      Row.bump lo.current.row scale ≤ hi.current.row := by
  have hSources : hi.sources = lo.sources :=
    Option.some.inj (hi.source_column.symm.trans lo.source_column)
  have hHigherAt : lo.sources[higher.index]? = some hi.current := by
    simpa only [hSources] using hi.current_at
  have hStrict := lo.source_valid.rows_strict _ _ _ _ lo.current_at hHigherAt hIndex
  obtain ⟨target, ceiling, degree, hRef, _, hHigh, hCeiling, hCap⟩ :=
    p.initial_marker_reference_below hLast hMap hLower lo.current_read hHigher hi.current_read hStrict
  have hTarget : target = lo.targetCell.row := Except.ok.inj (hRef.symm.trans lo.reference)
  exact ⟨degree, by simpa only [hTarget, hCeiling] using hHigh,
    by simpa only [hCeiling] using hCap⟩

/-- Preparation constructs the whole generic input record and also supplies
the two extra parent facts required by full fill-path power-step proofs. -/
theorem Preparation.first_column_copy_data_with_parent_rows {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∃ d : ColumnCopyData p.reduced p.marked references (p.root.column + 1)
        (p.reduced.size - 1 - p.root.column) p.root.column,
      (∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes) ∧
      (∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
        (d.marker_data marker hm).parentNodes[index]? = some cell ∧
          cell.row = (d.marker_data marker hm).current.row) := by
  classical
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRoot := p.root_before_last
  have hSourceBound : p.root.column + 1 < p.reduced.size := by omega
  let sources := p.reduced[p.root.column + 1]
  have hSources : p.reduced[p.root.column + 1]? = some sources :=
    Array.getElem?_eq_getElem hSourceBound
  let markerInput : ∀ marker, BucketMem p.marked (p.root.column + 1) marker →
      FirstSegmentData p references marker :=
    fun marker hm => Classical.choice (p.first_segment_data hLast hMap hm)
  let markerData : ∀ marker ∈ p.marked[p.root.column + 1]?.getD [],
      MarkerCopyData p.reduced sources references
        (p.reduced.size - 1 - p.root.column) marker.index :=
    fun marker hm => (markerInput marker hm).toMarkerCopyData hSources
  obtain ⟨_, hTop, hPower, hPositive⟩ := frozen_source_facts p.reduced_build
    (show PreservesColumns p.reduced p.reduced from fun _ _ => rfl) hSources
  let d : ColumnCopyData p.reduced p.marked references (p.root.column + 1)
      (p.reduced.size - 1 - p.root.column) p.root.column := {
    sources := sources
    ambient_valid := p.reduced_valid
    source_column := hSources
    source_nonzero := by omega
    destination := by omega
    source_top := hTop
    source_power := hPower
    source_positive := hPositive
    marker_columns := fun marker hm => (p.marker_iff.mp hm).1
    marker_order := (p.markers_ordered (p.root.column + 1)).1
    phantom_marker := p.phantom_marker (by omega) hSourceBound
    marker_data := markerData
    reference_zero := p.initial_referenceAt_zero hLast hMap
    reference_caps := by
      intro lower hLower higher hHigher hIndex
      exact (markerInput lower hLower).reference_cap (markerInput higher hHigher)
        hLast hMap hLower hHigher hIndex }
  refine ⟨d, ?_, ?_⟩
  · intro marker hm
    exact build_column_power_steps_of_read p.reduced_build (d.marker_data marker hm).parent_nodes
  · intro marker hm
    change ∃ (index : Nat) (cell : Cell), (markerInput marker hm).parentNodes[index]? = some cell ∧
      cell.row = (markerInput marker hm).current.row
    exact (markerInput marker hm).lower_parent_read hLast hm

theorem Preparation.first_column_copy_data {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    Nonempty (ColumnCopyData p.reduced p.marked references (p.root.column + 1)
      (p.reduced.size - 1 - p.root.column) p.root.column) := by
  obtain ⟨d, _, _⟩ := p.first_column_copy_data_with_parent_rows hLast hMap
  exact ⟨d⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.first_column_copy_data_with_parent_rows
#print axioms OmegaY.Expansion.Preparation.first_column_copy_data
