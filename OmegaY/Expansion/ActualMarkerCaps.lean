/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkerCaps.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootInterval

/-!
# Every actual marker cap lies below the original last top

Real markers use the partition selected at this block's actual boundary.
The phantom reference fixes zero and uses the cap one. Thus later high-row
preservation can take the original last top as a common threshold without
requiring any cap certificate from the caller.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem DynamicBlockState.marker_caps_below_lastTop
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    (hNext : next < p.reduced.size) :
    ∀ marker (hm : marker ∈ d.bucket), ∃ degree,
      (d.marker_data marker hm).targetCell.row < Row.bump (d.marker_data marker hm).current.row degree ∧
      Row.bump (d.marker_data marker hm).current.row degree ≤ p.lastTop.row := by
  intro marker hm
  let md := d.marker_data marker hm
  by_cases hZero : md.current.row = 0
  · have hTarget : md.targetCell.row = 0 := d.target_zero hm hZero
    refine ⟨0, ?_, ?_⟩
    · change md.targetCell.row < Row.bump md.current.row 0
      rw [hZero, hTarget, zero_bump_zero]
      exact Row.zero_lt_one
    · change Row.bump md.current.row 0 ≤ p.lastTop.row
      rw [hZero, zero_bump_zero]
      exact (p.top_row_gt_one hLast).le
  · have hSource : p.reduced[next]? = some d.sources :=
      (s.base_ambient next hNext).symm.trans d.source_column
    have hMarkerRead : Canonical.cellAt p.reduced marker = .ok md.current :=
      cellAt_ok_iff.mpr ⟨d.sources, by simpa only [d.marker_columns marker hm] using hSource, md.current_at⟩
    have hPositive : 0 < md.current.row := lt_of_le_of_ne (Row.zero_le _) (Ne.symm hZero)
    obtain ⟨index, ⟨a⟩⟩ := s.actual_marker_root_interval hLast hm hMarkerRead hPositive
    have hTarget : a.target.row = md.targetCell.row :=
      Except.ok.inj (a.ambient_query.symm.trans md.reference)
    exact ⟨a.degree, by rw [← hTarget]; exact a.target_below, a.cap_top⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.marker_caps_below_lastTop
