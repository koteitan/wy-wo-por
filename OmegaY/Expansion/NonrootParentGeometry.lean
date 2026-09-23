/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/NonrootParentGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RemainingInactiveGeometry

/-!
# Complete nonroot-parent classification of the actual residual geometry

The earlier parent's actual copied column supplies its greatest preceding
marker. Its real reference is either unraised, raised with the parent
inside the resulting root interval, or raised below a cap not exceeding
the parent. The marker-height equality case uses the physical marker
theorem. This classification adds no output Normal, parent selection,
copy-success, root-cone, or cap premise.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Every actual remaining stationary contour/seam whose frozen numerical
source father is strictly right of the bad-root column has exact raw
geometry. All controlling-marker and reference alternatives are derived
from the earlier actual column execution. -/
theorem DynamicBlockState.nonroot_parent_raw_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    {column : Column} {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row)
    (hRight : p.root.column < parent.1.val)
    (hLowerRead : column[index]? = some lower)
    (hUpperRead : column[index + 1]? = some upper) :
    CopiedRawAt ambient column lower upper := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hNext : next < p.reduced.size := by
    have h := child.1.isLt
    simpa only [Frame.ofMountain, hChildColumn] using h
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hBeforeNext : parent.1.val < next := by
    simpa only [hChildColumn] using Frame.P_column_lt hNormal.toOrdered hParent
  obtain ⟨before, parentColumn, pd, _, _, hParentSource, _, _, _, hQueries, _⟩ :=
    s.prior_column_data history hLast hRight hBeforeNext
  obtain ⟨marker, hm, hIndex, hNoBetween⟩ := pd.maximal_source_marker parent.2.val
  let md := pd.marker_data marker hm
  have hRead : Canonical.cellAt p.reduced marker = .ok md.current :=
    cellAt_ok_iff.mpr ⟨pd.sources,
      by simpa only [pd.marker_columns marker hm] using hParentSource, md.current_at⟩
  have hReference : referenceAt start references md.current.row = .ok md.targetCell.row :=
    ((hQueries md.current.row).trans (s.referenceAt_preserved md.current.row)).symm.trans md.reference
  have hAmbientReference : referenceAt ambient references md.current.row = .ok md.targetCell.row :=
    (s.referenceAt_preserved md.current.row).trans hReference
  have hParentRead := pd.frame_source_read hParentSource (rfl : parent.1.val = parent.1.val)
  have hLower : md.current.row ≤ F.height parent := pd.marker_source_row_le hm hParentRead hIndex
  obtain ⟨actualMarker, hMarkerRef, hMarkerCell⟩ := frame_node_of_cellAt (cellAt_ok_iff.mp hRead)
  have hMarkerColumn : actualMarker.1.val = parent.1.val :=
    (congrArg Ref.column hMarkerRef).trans (pd.marker_columns marker hm)
  have hMember : BucketMem p.marked actualMarker.1.val (Frame.ref actualMarker) := by
    rw [hMarkerColumn, hMarkerRef]
    exact hm
  have hMarkerRow : F.height actualMarker = md.current.row := congrArg Cell.row hMarkerCell
  rcases eq_or_lt_of_le hLower with hSame | hAbove
  · have hPositive : 0 < md.current.row := by
      rw [hSame]
      exact Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered
        (Frame.real_of_value_pos hNormal.toOrdered (Frame.P_value hNormal.toOrdered hParent).1))
    obtain ⟨rootIndex, ⟨a⟩⟩ := s.actual_marker_root_interval hLast hm hRead hPositive
    have hCone : Frame.RootCone F a.root parent :=
      (a.rootCone_of_marker hMember hMarkerRow).same_column (Fin.ext hMarkerColumn)
    exact s.remaining_marker_parent_geometry d hSource origin hParent hChildColumn hChildRow
      a hCone hSame.symm hRight hLowerRead hUpperRead
  · by_cases hRaised : md.current.row < md.targetCell.row
    · obtain ⟨rootIndex, a, hTarget, _⟩ :=
        s.raised_marker_root_interval hLast hm hRead hAmbientReference hRaised
      by_cases hInsideHeight : F.height parent < Row.bump md.current.row a.degree
      · have hInside : Frame.RootInterval F a.root (Row.bump md.current.row a.degree) parent :=
          a.inside_of_marker hMember hMarkerRow (Fin.ext hMarkerColumn) hLower hInsideHeight
        exact s.remaining_active_geometry history hLast d hSource origin hParent hChildColumn
          hChildRow a hInside hAbove hLowerRead hUpperRead
      · have hTargetCap : md.targetCell.row < Row.bump md.current.row a.degree := by
          rw [← hTarget]
          exact a.target_below
        exact s.remaining_inactive_geometry history hLast d origin hParent hChildColumn hChildRow
          hRight hm hRead hIndex hNoBetween hReference hTargetCap (le_of_not_gt hInsideHeight)
          hLowerRead hUpperRead
    · have hUnraised : md.targetCell.row = md.current.row :=
        le_antisymm (le_of_not_gt hRaised) md.target_lower
      have hIdentityReference : referenceAt start references md.current.row = .ok md.current.row := by
        simpa only [hUnraised] using hReference
      exact s.remaining_unraised_above_geometry history hLast d origin hParent hChildColumn hChildRow
        hRight hm hRead hIndex hNoBetween hIdentityReference hAbove hLowerRead hUpperRead

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.nonroot_parent_raw_geometry
