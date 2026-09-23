/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RemainingRootParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RemainingActiveGeometry
import OmegaY.Expansion.RemainingHighGeometry
import OmegaY.Expansion.ExactRootCap
import OmegaY.Expansion.ActualRootParentEdge
import OmegaY.Expansion.BadRootHighQuery

/-!
# All remaining source fathers in the root column

A low source father in the root column is proved to belong to the actual
bad-root prefix. Its reference interval is then constructed with a literal
cap from the executed boundary list. An interior prefix node cannot have
a child above that cap, by the source father-upper bound. At the bad root
itself, high boundary support supplies the larger-query selector.

Thus no source-prefix, cap, boundary-support, copied-normality, or desired
raw-geometry condition is added to the final residual interface.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem index_le_of_column_height {F : Frame} (hOrdered : F.Ordered)
    {node root : F.Node} (hColumn : node.1 = root.1)
    (hHeight : F.height node ≤ F.height root) : node.2.val ≤ root.2.val := by
  rcases node with ⟨c, i⟩
  dsimp only at hColumn
  subst c
  by_contra hn
  have hIndex : root.2 < i := Nat.lt_of_not_ge hn
  exact not_lt_of_ge hHeight ((hOrdered.rows_strict root.1) hIndex)

private theorem upper_exists_of_index_lt {F : Frame} {node later : F.Node}
    (hColumn : node.1 = later.1) (hIndex : node.2.val < later.2.val) :
    ∃ upper, F.upper node = some upper := by
  rcases node with ⟨c, i⟩
  dsimp only at hColumn
  subst c
  change i.val < later.2.val at hIndex
  have hBound : i.val + 1 < F.length later.1 := by have := later.2.isLt; omega
  exact ⟨⟨later.1, ⟨i.val + 1, hBound⟩⟩, by simp only [Frame.upper, hBound, ↓reduceDIte]⟩

/-- A real stored root-column row below the original last top is in the
bad-root prefix. The proof also covers a bad root with no upper node. -/
theorem Preparation.low_root_column_prefix {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParentColumn : parent.1.val = p.root.column)
    (hLow : (Frame.ofMountain p.reduced).height parent < p.lastTop.row) :
    parent.2.val ≤ p.root.index := by
  obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hColumn : parent.1 = badRoot.1 := Fin.ext
    (hParentColumn.trans (congrArg Ref.column hBadRef).symm)
  have hHeight := Frame.height_le_of_upper_barrier p.reduced_valid.toOrdered
    (fun upper hUpper => p.reduced_badRoot_upper_bound hLast hBadRef hUpper) hColumn hLow
  exact (index_le_of_column_height p.reduced_valid.toOrdered hColumn hHeight).trans
    (le_of_eq (congrArg Ref.index hBadRef))

/-- A low root-column parent supplies its own actual exact-cap reference
interval. Prefix membership and the original source read are derived. -/
theorem DynamicBlockState.exact_low_root_parent_interval
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParentColumn : parent.1.val = p.root.column)
    (hLow : (Frame.ofMountain p.reduced).height parent < p.lastTop.row)
    (hReal : Frame.Real parent) :
    ∃ b : ActualRootInterval p start ambient references parent.2.val
        ((Frame.ofMountain p.reduced).height parent),
      parent = b.root ∧
        Row.bump ((Frame.ofMountain p.reduced).height parent) b.degree ∈ p.boundaries := by
  have hPrefix := p.low_root_column_prefix hLast hParentColumn hLow
  have hParentRef : Frame.ref parent = ⟨p.root.column, parent.2.val⟩ := by
    simp only [Frame.ref, hParentColumn]
  have hInitialRead : Canonical.cellAt p.initial ⟨p.root.column, parent.2.val⟩ =
      .ok ((Frame.ofMountain p.reduced).cell parent) :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, parent.2.val⟩)
      p.initial_build p.reduced_build p.root_before_last).trans
      (by simpa only [hParentRef] using cellAt_of_frame_node p.reduced parent)
  obtain ⟨nodes, hColumn, hRead⟩ := cellAt_ok_iff.mp hInitialRead
  have hPositive : 0 < ((Frame.ofMountain p.reduced).cell parent).row :=
    Row.zero_lt_one.trans_le (Frame.one_le_height p.reduced_valid.toOrdered hReal)
  obtain ⟨a⟩ := s.actual_root_interval hLast hColumn hRead hPrefix hPositive
  obtain ⟨b, _, _, hMem⟩ := s.with_exact_root_cap hLast a
  exact ⟨b, Executable.ref_injective _ (hParentRef.trans b.root_ref.symm), hMem⟩

/-- Actual stationary contour/seam residuals are closed for every source
father in the root column. All prefix and cap facts are proved internally. -/
theorem DynamicBlockState.remaining_root_parent_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    (d : ColumnCopyData ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
    (hSource : p.reduced[next]? = some d.sources)
    {column : Column} {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row)
    (hParentColumn : parent.1.val = p.root.column)
    (hLowerRead : column[index]? = some lower)
    (hUpperRead : column[index + 1]? = some upper) :
    CopiedRawAt ambient column lower upper := by
  let F := Frame.ofMountain p.reduced
  by_cases hHigh : p.lastTop.row ≤ F.height parent
  · exact s.remaining_high_geometry history hLast hStartRun d origin hLowerRead hUpperRead
      hParent hChildColumn hChildRow hHigh
  have hLow : F.height parent < p.lastTop.row := lt_of_not_ge hHigh
  have hNormal := build_normal_of_success p.reduced_build
  have hParentReal : Frame.Real parent := Frame.real_of_value_pos hNormal.toOrdered
    (Frame.P_value hNormal.toOrdered hParent).1
  obtain ⟨b, hParentEq, hMem⟩ := s.exact_low_root_parent_interval hLast hParentColumn hLow hParentReal
  have hInside : Frame.RootInterval F b.root (Row.bump (F.height parent) b.degree) parent := by
    refine ⟨⟨b.root, b.root_real, (congrArg Sigma.fst hParentEq).symm, rfl, .refl _⟩, ?_, Row.lt_bump _ _⟩
    exact le_of_eq b.root_row
  obtain ⟨sourceUpper, originalUpper, hSourceUpper, hChildFixed, hUpperFixed, hActual, hShape⟩ :=
    origin.active_source_execution hSource hParent hChildColumn hChildRow b hInside
  have hEdge :
      copyEdge ambient (Frame.ref sourceUpper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift (F.height parent) b.target.row (F.height sourceUpper)) =
          .ok ⟨Row.lift (F.height parent) b.target.row (F.height sourceUpper), 0, some b.reference⟩ ∧
      Canonical.cellAt ambient b.reference = .ok b.target ∧
      b.reference.column = p.root.column + block * (p.reduced.size - 1 - p.root.column) ∧
      b.reference.column < ambient.size ∧
      b.target.row ≤ Row.lift (F.height parent) b.target.row (F.height child) ∧
      Row.lift (F.height parent) b.target.row (F.height sourceUpper) =
        Row.B (Row.lift (F.height parent) b.target.row (F.height child)) b.target.row := by
    by_cases hChildCap : F.height child < Row.bump (F.height parent) b.degree
    · exact s.copyEdge_root_parent_below_cap b hParent hParentEq hChildColumn hSourceUpper hChildCap
    have hCapChild : Row.bump (F.height parent) b.degree ≤ F.height child := le_of_not_gt hChildCap
    have hPrefix := b.root_prefix
    rcases lt_or_eq_of_le hPrefix with hBefore | hAtEnd
    · obtain ⟨badRoot, hBadRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
      have hColumn : parent.1 = badRoot.1 := Fin.ext
        (hParentColumn.trans (congrArg Ref.column hBadRef).symm)
      have hIndex : parent.2.val < badRoot.2.val := by
        simpa only [show badRoot.2.val = p.root.index from congrArg Ref.index hBadRef] using hBefore
      obtain ⟨parentUpper, hParentUpper⟩ := upper_exists_of_index_lt hColumn hIndex
      have hRootUpper : F.upper b.root = some parentUpper := by simpa only [← hParentEq] using hParentUpper
      have hCapEq := b.cap_eq_upper_of_boundary hLast hMem hBefore hRootUpper
      change Row.bump (F.height parent) b.degree = F.height parentUpper at hCapEq
      have hParentUpperLe : F.height parentUpper ≤ F.height child := by
        rw [← hCapEq]
        exact hCapChild
      have hFatherBound := Frame.father_upper_bound_nodes hNormal hParent hSourceUpper hParentUpper
      have hSourceB : F.height sourceUpper = Row.B (F.height child) (F.height parent) :=
        (Frame.aboveHeight_of_upper hSourceUpper).symm.trans (hNormal.above_row hParent)
      have hChildLt : F.height child < F.height sourceUpper :=
        (Row.lt_B (F.height child) (F.height parent)).trans_eq hSourceB.symm
      exact False.elim (not_lt_of_ge (hFatherBound.trans hParentUpperLe) hChildLt)
    · have hCap := b.cap_eq_lastTop_of_boundary hMem hAtEnd
      change Row.bump (F.height parent) b.degree = p.lastTop.row at hCap
      have hBadRoot : Frame.ref b.root = p.root := by simpa only [hAtEnd] using b.root_ref
      have hParentRef : Frame.ref parent = p.root := (congrArg Frame.ref hParentEq).trans hBadRoot
      have hChildHigh : p.lastTop.row ≤ F.height child := by rw [← hCap]; exact hCapChild
      have hBelow := (s.below_badRoot_high_query hLast hStartRun b hBadRoot hCap hParent
        hParentRef hSourceUpper hChildHigh).1
      apply s.copyEdge_root_parent_of_below b hParent hParentEq hChildColumn hSourceUpper
      rw [hUpperFixed, ← s.boundary_copy_index]
      exact hBelow
  obtain ⟨hExpected, hRead, _, hBefore, hBound, hB⟩ := hEdge
  rw [hUpperFixed] at hExpected hB
  rw [hChildFixed] at hBound hB
  have hEqual : (⟨F.height sourceUpper, 0, some b.reference⟩ : Cell) = originalUpper :=
    Except.ok.inj (hExpected.symm.trans hActual)
  have hOriginalLeft : originalUpper.left = some b.reference := by rw [← hEqual]
  have hOriginalRow : originalUpper.row = F.height sourceUpper := by rw [← hEqual]
  have hOutputLeft : upper.left = some b.reference := hShape.2.symm.trans hOriginalLeft
  have hOutputB : upper.row = Row.B lower.row b.target.row := by
    rw [← hChildRow]
    exact hShape.1.symm.trans (hOriginalRow.trans hB)
  exact ⟨b.reference, b.target, hOutputLeft, (cellAt_push_left hBefore).trans hRead,
    hBefore, hChildRow ▸ hBound, hOutputB⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.low_root_column_prefix
#print axioms OmegaY.Expansion.DynamicBlockState.exact_low_root_parent_interval
#print axioms OmegaY.Expansion.DynamicBlockState.remaining_root_parent_geometry
