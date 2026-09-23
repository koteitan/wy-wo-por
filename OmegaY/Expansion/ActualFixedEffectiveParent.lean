/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFixedEffectiveParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveParent
import OmegaY.Expansion.WeakParentPaths
import OmegaY.Expansion.AdjacentMarkerExecution

/-!
# Effective contour edges with fixed good-part parents

An actual source edge leaving the bad part cannot start at a real marker.
Both executed contour adjacency and a following marker seam retain the
original parent reference. The effective child may have been raised; no
target numerical parent recognition is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem Preparation.fixed_parent_not_marked {front : List Nat} {last : Nat}
    (p : Preparation front last) {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hFixed : parent.1.val < p.root.column) :
    ¬ BucketMem p.marked child.1.val (Frame.ref child) := by
  intro hMarked
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨hRight, low, _, hColumn, _, hPath, _⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hReal).mp hMarked
  have hRootColumn : root.1.val = p.root.column := congrArg Ref.column hRootRef
  cases hPath with
  | refl =>
    have hSame := congrArg Fin.val hColumn
    omega
  | @cons child next low hNext tail =>
    have he : next = parent := Option.some.inj (hNext.symm.trans hParent)
    subst next
    have hLow := tail.column_le hNormal.toOrdered
    have hSame := congrArg Fin.val hColumn
    omega

/-- Actual effective-child/fixed-parent correspondence, including a source
upper which is the next marker. All target reads and the actual copy request
are constructed from the real copy state. -/
theorem DynamicBlockState.actual_fixed_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hFixed : parent.1.val < p.root.column)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      RawRefEdge (ambient.push column) childCopy.outputRef (Frame.ref parent) ∧
      Canonical.cellAt (ambient.push column) (Frame.ref parent) =
        .ok ((Frame.ofMountain p.reduced).cell parent) := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨sourceUpper, hUpper⟩ := hNormal.upper_of_parent hParent
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead : d.sources[child.2.val]? = some (F.cell child) := by
    rw [← (Array.getElem?_eq_some_iff.mp hSource).2]
    exact Array.getElem?_eq_getElem child.2.isLt
  have hUpperRef : Frame.ref sourceUpper = ⟨child.1.val, child.2.val + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  have hSourceUpper : d.sources[child.2.val + 1]? = some (F.cell sourceUpper) := by
    obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp (cellAt_of_frame_node p.reduced sourceUpper)
    rw [hUpperRef] at hNodes hRead
    have he : nodes = d.sources := Option.some.inj (hNodes.symm.trans hSource)
    exact he ▸ hRead
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
  obtain ⟨upper, copied, queryRow, hHi, hCopy, hShape⟩ :
      ∃ (upper copied : Cell) (queryRow : Row),
        column[read.outputIndex + 1]? = some upper ∧
        copyEdge ambient ⟨child.1.val, child.2.val + 1⟩
          (block * (p.reduced.size - 1 - p.root.column)) p.root.column queryRow = .ok copied ∧
        SameShape copied upper := by
    by_cases hUpperMarked : child.2.val + 1 ∈ d.bucket.map Ref.index
    · obtain ⟨upper, copied, hHi, _, hCopy, hShape⟩ :=
        d.effective_upper_marker_execution hParentPower hParentLow hNoPremature
          read hSourceUpper hUpperMarked
      exact ⟨upper, copied, (F.cell sourceUpper).row, hHi, hCopy, hShape⟩
    ·
      have hAfter : read.marker.index < child.2.val := by
        have hBefore := read.marker_before
        have hNe : read.marker.index ≠ child.2.val := by
          intro hEq
          have hRefEq : read.marker = Frame.ref child := by
            cases hm : read.marker with
            | mk c i =>
              have hc := d.marker_columns read.marker read.marker_mem
              simp only [hm, Ref.mk.injEq, Frame.ref] at hc hEq ⊢
              exact ⟨hc, hEq⟩
          exact p.fixed_parent_not_marked hParent hFixed (hRefEq ▸ read.marker_mem)
        omega
      have hNoBetween : ∀ middle, read.marker.index < middle → middle ≤ child.2.val + 1 →
          middle ∉ d.bucket.map Ref.index := by
        intro middle hLow hHigh
        by_cases hLe : middle ≤ child.2.val
        · exact read.no_between middle hLow hLe
        · have he : middle = child.2.val + 1 := by omega
          exact he ▸ hUpperMarked
      obtain ⟨position, lower, upper, copied, hLo, hHi, hLoRow, _, hCopy, hShape⟩ :=
        d.copyColumn_source_adjacent_execution hParentPower hParentLow hNoPremature hRun
          read.marker_mem hChildRead hSourceUpper hAfter hNoBetween
      obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
      have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
      subst actual
      have hIndex : position = read.outputIndex :=
        column_read_index_eq_of_row hValid hLo read.output_at (hLoRow.trans read.output_row.symm)
      exact ⟨upper, copied, _, by simpa only [hIndex] using hHi, hCopy, hShape⟩
  have hChildReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldParent, hOldParent, _, _, hStored⟩ := hNormal.upper_step child sourceUpper hChildReal hUpper
  have hOldEq : oldParent = parent := Option.some.inj (hOldParent.symm.trans hParent)
  subst oldParent
  change (F.cell sourceUpper).left = some (Frame.ref parent) at hStored
  have hLookup : lookup ambient ⟨child.1.val, child.2.val + 1⟩ = .ok (F.cell sourceUpper) :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, hSourceUpper⟩
  have hNonzero : (F.cell sourceUpper).row ≠ 0 := ne_of_gt
    (Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered (upper_real hUpper)))
  have hDestination : (Frame.ref parent).column < child.1.val +
      block * (p.reduced.size - 1 - p.root.column) :=
    (Frame.P_column_lt hNormal.toOrdered hParent).trans_le (Nat.le_add_right _ _)
  have hFixedRef : (Frame.ref parent).column < p.root.column := hFixed
  have hCopied : (⟨queryRow, 0, some (Frame.ref parent)⟩ : Cell) = copied := by
    simpa [copyEdge, hLookup, hNonzero, leftOf, hStored, hFixedRef,
      Nat.not_le_of_gt hDestination] using hCopy
  have hCopiedLeft : copied.left = some (Frame.ref parent) := congrArg Cell.left hCopied.symm
  have hParentRead : Canonical.cellAt ambient (Frame.ref parent) = .ok (F.cell parent) :=
    p.cell_read_preserved s.base_ambient (Canonical.cellAt_of_frame_node p.reduced parent)
  have hFinalParent : Canonical.cellAt (ambient.push column) (Frame.ref parent) = .ok (F.cell parent) := by
    obtain ⟨nodes, hNodes, hRead⟩ := cellAt_ok_iff.mp hParentRead
    exact cellAt_ok_iff.mpr ⟨nodes, (PreservesColumns.push ambient column).column_read hNodes, hRead⟩
  let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
    ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
  refine ⟨childCopy, rfl, rfl, ?_, hFinalParent⟩
  refine ⟨read.outputCell, upper, F.cell parent, read.output_read, ?_,
    hShape.2.symm.trans hCopiedLeft, hFinalParent⟩
  exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
    EffectiveCopyRead.outputRef], by
      change column[read.outputIndex + 1]? = some upper
      exact hHi⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.fixed_parent_not_marked
#print axioms OmegaY.Expansion.DynamicBlockState.actual_fixed_parent
