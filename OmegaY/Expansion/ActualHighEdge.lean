/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighEdge.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighParent

/-!
# Actual copyEdge geometry for high source parents

Source parents at or above the original last top force their child and
upper above every actual marker cap. These source rows are fixed by each
marker lift. Actual parent selection covers fixed good-part parents,
copied non-root parents, and the boundary representing the root column.
Only the source mountain is assumed normal, via its successful build.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Every actual marker lift fixes the child and its upper when its
numerical source parent is at or above the original last top. This
derives the unchanged copy request from actual reference caps. -/
theorem DynamicBlockState.high_parent_lifts_fixed
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent)
    {marker : Ref} (hm : marker ∈ d.bucket) :
    Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row
      ((Frame.ofMountain p.reduced).height child) = (Frame.ofMountain p.reduced).height child ∧
    Row.lift (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row
      ((Frame.ofMountain p.reduced).height upper) = (Frame.ofMountain p.reduced).height upper := by
  have hNormal := build_normal_of_success p.reduced_build
  have hNext : next < p.reduced.size := hChildColumn ▸ child.1.isLt
  obtain ⟨degree, hTarget, hCap⟩ := s.marker_caps_below_lastTop hLast d hNext marker hm
  have hParentLe := Frame.P_height_le hNormal.toOrdered hParent
  have hUpperRow : (Frame.ofMountain p.reduced).height upper =
      Row.B ((Frame.ofMountain p.reduced).height child) ((Frame.ofMountain p.reduced).height parent) :=
    (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
  have hChildLt : (Frame.ofMountain p.reduced).height child < (Frame.ofMountain p.reduced).height upper := by
    rw [hUpperRow]
    exact Row.lt_B _ _
  exact ⟨Row.lift_eq_of_ge_cap (d.marker_data marker hm).target_lower hTarget
      (hCap.trans (hHigh.trans hParentLe)),
    Row.lift_eq_of_ge_cap (d.marker_data marker hm).target_lower hTarget
      (hCap.trans (hHigh.trans (hParentLe.trans hChildLt.le)))⟩

/-- The actual copied upper edge for a high numerical source parent,
including every parent-column case. The outer-loop run is used only in
the root-boundary case; it supplies its high-tail support constructively.
No copy success, output adjacency, or new numerical-parent condition is
provided by the caller. -/
theorem DynamicBlockState.copyEdge_high_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent) :
    ∃ (copied : Cell) (actualRef : Ref) (actualParent : Cell),
      copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        ((Frame.ofMountain p.reduced).height upper) = .ok copied ∧
      copied.row = (Frame.ofMountain p.reduced).height upper ∧
      copied.value = 0 ∧ copied.left = some actualRef ∧
      actualRef.column = (if parent.1.val < p.root.column then parent.1.val else
        parent.1.val + block * (p.reduced.size - 1 - p.root.column)) ∧
      actualRef.column < ambient.size ∧
      Canonical.cellAt ambient actualRef = .ok actualParent ∧
      actualParent.row = (Frame.ofMountain p.reduced).height parent ∧
      actualParent.row ≤ (Frame.ofMountain p.reduced).height child ∧
      copied.row = Row.B ((Frame.ofMountain p.reduced).height child) actualParent.row := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hChildReal : Frame.Real child := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldParent, hOldParent, hRow, _, hStored⟩ := hNormal.upper_step child upper hChildReal hUpper
  have he : oldParent = parent := Option.some.inj (hOldParent.symm.trans hParent)
  subst oldParent
  change (F.cell upper).left = some (Frame.ref parent) at hStored
  have hSourceRead : lookup ambient (Frame.ref upper) = .ok (F.cell upper) :=
    lookup_ok_iff.mpr (cellAt_ok_iff.mp
      (p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced upper)))
  have hUpperReal : Frame.Real upper := upper_real hUpper
  have hNonzero : (F.cell upper).row ≠ 0 := by
    intro hz
    have hPositive := Frame.one_le_height hNormal.toOrdered hUpperReal
    change (1 : Row) ≤ (F.cell upper).row at hPositive
    rw [hz] at hPositive
    exact (not_le_of_gt Row.zero_lt_one) hPositive
  have hParentLeft : parent.1.val < upper.1.val := by
    rw [(Frame.upper_spec hUpper).1]
    exact Frame.P_column_lt hNormal.toOrdered hParent
  have hUpperColumn : (Frame.ref upper).column = next :=
    (congrArg Fin.val (Frame.upper_spec hUpper).1).trans hChildColumn
  have hParentLe : F.height parent ≤ F.height child := Frame.P_height_le hNormal.toOrdered hParent
  by_cases hFixed : parent.1.val < p.root.column
  · have hRead : Canonical.cellAt ambient (Frame.ref parent) = .ok (F.cell parent) :=
      p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced parent)
    have hDestination : (Frame.ref parent).column <
        (Frame.ref upper).column + block * (p.reduced.size - 1 - p.root.column) := by
      change parent.1.val < upper.1.val + _
      omega
    have hAmbient : (Frame.ref parent).column < ambient.size := by
      rw [s.size_eq, ← hUpperColumn]
      exact hDestination
    let copied : Cell := ⟨F.height upper, 0, some (Frame.ref parent)⟩
    refine ⟨copied, Frame.ref parent, F.cell parent, ?_, rfl, rfl, rfl,
      by simp only [hFixed, ↓reduceIte, Frame.ref], hAmbient, hRead, rfl, hParentLe, hRow⟩
    have hFixedRef : (Frame.ref parent).column < p.root.column := hFixed
    simp [copyEdge, copied, hSourceRead, hNonzero, leftOf, hStored, hFixedRef,
      Nat.not_le_of_gt hDestination]
    rfl
  · have hExecutable : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent) :=
      (Executable.findParent_ref_iff hNormal.toOrdered child parent).mpr hParent
    have hSelected : ∃ (ref : Ref) (cell : Cell),
        below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
          (F.height upper) = .ok ref ∧
        Canonical.cellAt ambient ref = .ok cell ∧
        ref.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
        cell.row = F.height parent := by
      rcases eq_or_lt_of_le (Nat.le_of_not_gt hFixed) with hRoot | hRight
      · simpa only [hRoot] using s.below_high_root_parent hLast hStartRun hExecutable hUpper hRoot.symm hHigh
      · exact s.below_high_parent history hLast hExecutable hChildColumn hUpper hRight hHigh
    obtain ⟨actualRef, actualParent, hBelow, hRead, hColumn, hParentRow⟩ := hSelected
    have hDestination : actualRef.column <
        (Frame.ref upper).column + block * (p.reduced.size - 1 - p.root.column) := by
      rw [hColumn]
      exact Nat.add_lt_add_right hParentLeft _
    have hAmbient : actualRef.column < ambient.size := by
      rw [s.size_eq, ← hUpperColumn]
      exact hDestination
    let copied : Cell := ⟨F.height upper, 0, some actualRef⟩
    refine ⟨copied, actualRef, actualParent, ?_, rfl, rfl, rfl,
      by simpa only [hFixed, ↓reduceIte] using hColumn, hAmbient, hRead, hParentRow,
      hParentRow ▸ hParentLe, ?_⟩
    · change below ambient ((Frame.ref parent).column + block * (p.reduced.size - 1 - p.root.column))
        ((Frame.ofMountain p.reduced).height upper) = .ok actualRef at hBelow
      have hNotFixed : ¬ (Frame.ref parent).column < p.root.column := hFixed
      simp [copyEdge, copied, hSourceRead, hNonzero, leftOf, hStored, hNotFixed,
        hBelow, Nat.not_le_of_gt hDestination]
      rfl
    · change F.height upper = Row.B (F.height child) actualParent.row
      rw [hParentRow]
      exact hRow

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.high_parent_lifts_fixed
#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_high_parent
