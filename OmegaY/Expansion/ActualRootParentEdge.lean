/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootParentEdge.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootInterval
import OmegaY.Expansion.MarkerParentInterval

/-!
# Actual copyEdge at a source parent in the root column itself

The source P edge supplies its complete stored leg and B equation. An
already established boundary selector is enough to execute copyEdge. In
the below-cap case that selector is derived by lowering the actual
reference-query ceiling. No positive degree, raised target, output
normality, or new copy success is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Reusable execution interface once the exact boundary selector has
been proved. The B equation and parent-row bound are still conclusions.
The selected read is the actual reference cell retained by the interval. -/
theorem DynamicBlockState.copyEdge_root_parent_of_below
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next rootIndex : Nat} {rootRow : Row}
    (s : DynamicBlockState p block start references next ambient)
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hParentEq : parent = a.root) (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hBelow : below ambient (start.size - 1)
      (Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height upper)) = .ok a.reference) :
    copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height upper)) =
        .ok ⟨Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height upper), 0, some a.reference⟩ ∧
      Canonical.cellAt ambient a.reference = .ok a.target ∧
      a.reference.column = p.root.column + block * (p.reduced.size - 1 - p.root.column) ∧
      a.reference.column < ambient.size ∧
      a.target.row ≤ Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child) ∧
      Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height upper) =
        Row.B (Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child)) a.target.row := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hParentRow : F.height parent = rootRow := hParentEq ▸ a.root_row
  have hParentColumn : parent.1.val = p.root.column :=
    (congrArg (fun node => node.1.val) hParentEq).trans (congrArg Ref.column a.root_ref)
  have hRootChild : rootRow ≤ F.height child := by
    have hLe : F.height parent ≤ F.height child := Frame.P_height_le hNormal.toOrdered hParent
    exact hParentRow ▸ hLe
  have hUpperRow : F.height upper = Row.B (F.height child) rootRow := by
    have hB := (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
    simpa only [hParentEq, a.root_row] using hB
  have hB : Row.lift rootRow a.target.row (F.height upper) =
      Row.B (Row.lift rootRow a.target.row (F.height child)) a.target.row := by
    rw [hUpperRow, Row.lift_B hRootChild le_rfl, Row.lift_at_root]
  have hTargetLow : a.target.row ≤ Row.lift rootRow a.target.row (F.height child) := by
    have h := Row.lift_monotone (root := rootRow) (t := a.target.row) le_rfl hRootChild
    simpa only [Row.lift_at_root] using h
  have hChildReal : Frame.Real child := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldParent, hOldParent, _, _, hStored⟩ := hNormal.upper_step child upper hChildReal hUpper
  have he : oldParent = parent := Option.some.inj (hOldParent.symm.trans hParent)
  subst oldParent
  change (F.cell upper).left = some (Frame.ref parent) at hStored
  have hSource : lookup ambient (Frame.ref upper) = .ok (F.cell upper) :=
    lookup_ok_iff.mpr (cellAt_ok_iff.mp
      (p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced upper)))
  have hNonzero : (F.cell upper).row ≠ 0 := by
    have hOne := Frame.one_le_height hNormal.toOrdered (upper_real hUpper)
    intro hz
    change (1 : Row) ≤ (F.cell upper).row at hOne
    rw [hz] at hOne
    exact (not_le_of_gt Row.zero_lt_one) hOne
  have hReferenceColumn : a.reference.column = p.root.column +
      block * (p.reduced.size - 1 - p.root.column) := a.reference_column.trans s.boundary_copy_index.symm
  have hUpperColumn : (Frame.ref upper).column = next :=
    (congrArg Fin.val (Frame.upper_spec hUpper).1).trans hChildColumn
  have hDestination : a.reference.column < (Frame.ref upper).column +
      block * (p.reduced.size - 1 - p.root.column) := by
    rw [hReferenceColumn, hUpperColumn]
    exact Nat.add_lt_add_right s.next_lower _
  have hBefore : a.reference.column < ambient.size := by
    rw [s.size_eq, ← hUpperColumn]
    exact hDestination
  refine ⟨?_, a.target_ambient_read, hReferenceColumn, hBefore, hTargetLow, hB⟩
  have hParentRefColumn : (Frame.ref parent).column = p.root.column := hParentColumn
  have hSelected : below ambient ((Frame.ref parent).column +
      block * (p.reduced.size - 1 - p.root.column))
      (Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height upper)) = .ok a.reference := by
    rw [hParentRefColumn, s.boundary_copy_index]
    exact hBelow
  have hNotFixed : ¬ (Frame.ref parent).column < p.root.column := by rw [hParentRefColumn]; omega
  simp [copyEdge, hSource, hNonzero, leftOf, hStored, hNotFixed, hSelected,
    Nat.not_le_of_gt hDestination]

/-- For a source child below this actual reference cap, lowering the
boundary ceiling proves the selector needed by copyEdge. This includes
degree zero and unraised reference targets. -/
theorem DynamicBlockState.copyEdge_root_parent_below_cap
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next rootIndex : Nat} {rootRow : Row}
    (s : DynamicBlockState p block start references next ambient)
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hParentEq : parent = a.root) (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hChildCap : (Frame.ofMountain p.reduced).height child < Row.bump rootRow a.degree) :
    copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height upper)) =
        .ok ⟨Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height upper), 0, some a.reference⟩ ∧
      Canonical.cellAt ambient a.reference = .ok a.target ∧
      a.reference.column = p.root.column + block * (p.reduced.size - 1 - p.root.column) ∧
      a.reference.column < ambient.size ∧
      a.target.row ≤ Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child) ∧
      Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height upper) =
        Row.B (Row.lift rootRow a.target.row ((Frame.ofMountain p.reduced).height child)) a.target.row := by
  have hNormal := build_normal_of_success p.reduced_build
  have hRootChild : rootRow ≤ (Frame.ofMountain p.reduced).height child := by
    simpa only [hParentEq, a.root_row] using Frame.P_height_le hNormal.toOrdered hParent
  have hUpperRow : (Frame.ofMountain p.reduced).height upper =
      Row.B ((Frame.ofMountain p.reduced).height child) rootRow := by
    have h := (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
    simpa only [hParentEq, a.root_row] using h
  obtain ⟨nodes, hNodes, hTargetRead⟩ := cellAt_ok_iff.mp a.target_ambient_read
  rw [a.reference_column] at hNodes
  have hBelow := (below_boundary_root_parent hNodes a.ambient_below hTargetRead
    a.target_lower hRootChild hChildCap).1
  exact s.copyEdge_root_parent_of_below a hParent hParentEq hChildColumn hUpper
    (by simpa only [hUpperRow] using hBelow)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_root_parent_of_below
#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_root_parent_below_cap
