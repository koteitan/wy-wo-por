/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkerTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMarkerCone

/-!
# Exhaustive row transport at a real executed marker

An actual reference either leaves its marker fixed, or is genuinely raised.
In the latter case the real boundary partition supplies the unique queried
target and an interval certificate. A source node controlled by the marker
then belongs to that root interval or lies beyond its cap, where its row
is fixed. The interval/cone data are conclusions of the executable marker
and reference construction.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Source index order gives the lower row bound, including equality at
the physical marker. -/
theorem ColumnCopyData.marker_source_row_le
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    {marker : Ref} (hm : marker ∈ d.bucket) {sourceIndex : Nat} {source : Cell}
    (hSource : d.sources[sourceIndex]? = some source) (hAfter : marker.index ≤ sourceIndex) :
    (d.marker_data marker hm).current.row ≤ source.row := by
  rcases eq_or_lt_of_le hAfter with he | hl
  · have hSame : (d.marker_data marker hm).current = source :=
      Option.some.inj ((d.marker_data marker hm).current_at.symm.trans
        (by simpa only [he] using hSource))
    exact le_of_eq (congrArg Cell.row hSame)
  · exact (d.source_valid.rows_strict _ _ _ _ (d.marker_data marker hm).current_at hSource hl).le

/-- No independent root, cap, target-read, or root-cone premise is needed
for this exhaustive classification of the actual marker's row transform. -/
theorem DynamicBlockState.marker_source_transport
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    {node : (Frame.ofMountain p.reduced).Node} (hColumn : node.1.val = next)
    (hAfter : marker.index ≤ node.2.val) :
    ((d.marker_data marker hm).targetCell.row = (d.marker_data marker hm).current.row ∧
      Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row
        ((Frame.ofMountain p.reduced).height node) = (Frame.ofMountain p.reduced).height node) ∨
    ∃ index, ∃ a : ActualRootInterval p start ambient references index (d.marker_data marker hm).current.row,
      a.target.row = (d.marker_data marker hm).targetCell.row ∧
      (d.marker_data marker hm).current.row < a.target.row ∧
      (Frame.RootInterval (Frame.ofMountain p.reduced) a.root
        (Row.bump (d.marker_data marker hm).current.row a.degree) node ∨
        (Row.bump (d.marker_data marker hm).current.row a.degree ≤
            (Frame.ofMountain p.reduced).height node ∧
          Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row
            ((Frame.ofMountain p.reduced).height node) = (Frame.ofMountain p.reduced).height node)) := by
  let md := d.marker_data marker hm
  have hNext : next < p.reduced.size := by
    have h := node.1.isLt
    simpa only [Frame.ofMountain, hColumn] using h
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hNodeRead := d.frame_source_read hSource hColumn
  have hLower := d.marker_source_row_le hm hNodeRead hAfter
  by_cases hRaised : md.current.row < md.targetCell.row
  · have hMarkerRead : Canonical.cellAt p.reduced marker = .ok md.current :=
      cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns marker hm] using hSource, md.current_at⟩
    obtain ⟨index, a, hTarget, _⟩ := s.raised_marker_root_interval hLast hm hMarkerRead md.reference hRaised
    refine Or.inr ⟨index, a, hTarget, by rw [hTarget]; exact hRaised, ?_⟩
    by_cases hInside : (Frame.ofMountain p.reduced).height node < Row.bump md.current.row a.degree
    · exact Or.inl (d.actual_marker_source_interval hSource a hm rfl hColumn hAfter hInside)
    · refine Or.inr ⟨le_of_not_gt hInside, ?_⟩
      exact Row.lift_eq_of_ge_cap md.target_lower (by rw [← hTarget]; exact a.target_below)
        (le_of_not_gt hInside)
  · have hSame : md.targetCell.row = md.current.row :=
      le_antisymm (le_of_not_gt hRaised) md.target_lower
    refine Or.inl ⟨hSame, ?_⟩
    change Row.lift md.current.row md.targetCell.row ((Frame.ofMountain p.reduced).height node) = _
    rw [hSame]
    exact Row.lift_identity hLower

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.marker_source_row_le
#print axioms OmegaY.Expansion.DynamicBlockState.marker_source_transport
