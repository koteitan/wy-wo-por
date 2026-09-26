/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/StationaryContourGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RaisedContourGeometry
import OmegaY.Expansion.DynamicActiveParent

/-!
# Fixed-column and active-parent contour geometry

A stationary child can have a moved parent. The active-parent theorem
therefore assumes only that the source father lies strictly inside the
actual reference interval; the child may be beyond its cap. Separately,
when the program fixes the father's column, stationarity of the lower
row forces the upper bump to be stationary and the old father is retained.

The final wrappers recover source nodes and P from actual contour reads.
The remaining active-interval premise concerns that source father, not
output normality, a desired copied parent, or a successful individual copy.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem source_upper_parent_data
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper) :
    lookup ambient (Frame.ref upper) = .ok ((Frame.ofMountain p.reduced).cell upper) ∧
    ((Frame.ofMountain p.reduced).cell upper).left = some (Frame.ref parent) ∧
    ((Frame.ofMountain p.reduced).cell upper).row ≠ 0 ∧
    (Frame.ofMountain p.reduced).height upper = Row.B
      ((Frame.ofMountain p.reduced).height child) ((Frame.ofMountain p.reduced).height parent) ∧
    Canonical.cellAt ambient (Frame.ref parent) = .ok ((Frame.ofMountain p.reduced).cell parent) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hChildReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨actualParent, hActualParent, hB, _, hStored⟩ :=
    hNormal.upper_step child upper hChildReal hUpper
  have hSame : actualParent = parent := Option.some.inj (hActualParent.symm.trans hParent)
  subst actualParent
  have hUpperReal : Frame.Real upper := by
    have hi := (Frame.upper_spec hUpper).2
    unfold Frame.Real
    omega
  have hNonzero : ((Frame.ofMountain p.reduced).cell upper).row ≠ 0 := by
    intro hz
    have hPositive := Frame.one_le_height hNormal.toOrdered hUpperReal
    change (1 : Row) ≤ ((Frame.ofMountain p.reduced).cell upper).row at hPositive
    rw [hz] at hPositive
    exact (not_le_of_gt Row.zero_lt_one) hPositive
  exact ⟨lookup_ok_iff.mpr (cellAt_ok_iff.mp
      (p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced upper))),
    hStored, hNonzero, hB,
    p.cell_read_preserved s.base_ambient (cellAt_of_frame_node p.reduced parent)⟩

/-- The actual active-parent selector applies even when the child is
outside the cap. This is the exact individual copy, with a readable lifted
father, the parent-row bound, and B. Target stationarity is allowed. -/
theorem DynamicBlockState.copyEdge_active_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceIndex : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references sourceIndex sourceRow)
    {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hParentInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump sourceRow a.degree) parent)
    (hParentAbove : sourceRow < (Frame.ofMountain p.reduced).height parent)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper) :
    ∃ (copied : Cell) (actualRef : Ref) (actualParent : Cell),
      copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper)) = .ok copied ∧
      copied.row = Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper) ∧
      copied.left = some actualRef ∧
      actualRef.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      Canonical.cellAt ambient actualRef = .ok actualParent ∧
      actualParent.row = Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height parent) ∧
      actualParent.row ≤ Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height child) ∧
      copied.row = Row.B (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height child))
        actualParent.row := by
  let F := Frame.ofMountain p.reduced
  obtain ⟨newIndex, actualParent, hBelow, hRead, hParentRow⟩ :=
    s.actual_active_parent history hLast a hParentInside hParentAbove hParent hChildColumn hUpper
  let actualRef : Ref := ⟨parent.1.val + block * (p.reduced.size - 1 - p.root.column), newIndex⟩
  obtain ⟨hSource, hStored, hNonzero, hSourceB, _⟩ := source_upper_parent_data s hParent hUpper
  have hNormal := build_normal_of_success p.reduced_build
  have hParentLow : sourceRow ≤ F.height parent := by
    simpa only [a.root_row] using hParentInside.2.1
  have hChildLow : sourceRow ≤ F.height child :=
    hParentLow.trans (Frame.P_height_le hNormal.toOrdered hParent)
  have hMoved : ¬ (Frame.ref parent).column < p.root.column := by
    have hc := Frame.RootCone.column_le hNormal.toOrdered hParentInside.1
    have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
    change ¬ parent.1.val < p.root.column
    rw [hRootColumn] at hc
    exact Nat.not_lt_of_ge hc
  have hDestination : actualRef.column <
      (Frame.ref upper).column + block * (p.reduced.size - 1 - p.root.column) := by
    apply Nat.add_lt_add_right
    change parent.1.val < upper.1.val
    rw [(Frame.upper_spec hUpper).1]
    exact Frame.P_column_lt hNormal.toOrdered hParent
  let copied : Cell := ⟨Row.lift sourceRow a.target.row (F.height upper), 0, some actualRef⟩
  refine ⟨copied, actualRef, actualParent, ?_, rfl, rfl, rfl, hRead, hParentRow, ?_, ?_⟩
  · change below ambient ((Frame.ref parent).column + block * (p.reduced.size - 1 - p.root.column))
      (Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height upper)) = .ok actualRef at hBelow
    simp [copyEdge, copied, hSource, hNonzero, leftOf, hStored, hMoved, hBelow,
      Nat.not_le_of_gt hDestination]
    rfl
  · rw [hParentRow]
    exact Row.lift_monotone hParentLow (Frame.P_height_le hNormal.toOrdered hParent)
  · change Row.lift sourceRow a.target.row (F.height upper) = _
    rw [hSourceB, hParentRow]
    exact Row.lift_B hChildLow hParentLow

/-- For a fixed-column father, a stationary lower row makes its actual
upper bump stationary too. No assertion about moved fathers is used. -/
theorem DynamicBlockState.copyEdge_stationary_fixed_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    {root target : Row} {child parent upper : (Frame.ofMountain p.reduced).Node}
    (hRootChild : root ≤ (Frame.ofMountain p.reduced).height child)
    (hStationary : Row.lift root target ((Frame.ofMountain p.reduced).height child) =
      (Frame.ofMountain p.reduced).height child)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some upper)
    (hFixed : parent.1.val < p.root.column) :
    copyEdge ambient (Frame.ref upper) (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift root target ((Frame.ofMountain p.reduced).height upper)) =
      .ok ⟨(Frame.ofMountain p.reduced).height upper, 0, some (Frame.ref parent)⟩ ∧
    Canonical.cellAt ambient (Frame.ref parent) = .ok ((Frame.ofMountain p.reduced).cell parent) ∧
    (Frame.ofMountain p.reduced).height parent ≤
      Row.lift root target ((Frame.ofMountain p.reduced).height child) ∧
    (Frame.ofMountain p.reduced).height upper =
      Row.B (Row.lift root target ((Frame.ofMountain p.reduced).height child))
        ((Frame.ofMountain p.reduced).height parent) := by
  obtain ⟨hSource, hStored, hNonzero, hSourceB, hParentRead⟩ := source_upper_parent_data s hParent hUpper
  have hNormal := build_normal_of_success p.reduced_build
  have hUpperFixed : Row.lift root target ((Frame.ofMountain p.reduced).height upper) =
      (Frame.ofMountain p.reduced).height upper := by
    rw [hSourceB, Row.B, Row.lift_bump hRootChild, hStationary]
  have hLeftward : (Frame.ref parent).column < (Frame.ref upper).column := by
    change parent.1.val < upper.1.val
    rw [(Frame.upper_spec hUpper).1]
    exact Frame.P_column_lt hNormal.toOrdered hParent
  have hDestination : (Frame.ref parent).column <
      (Frame.ref upper).column + block * (p.reduced.size - 1 - p.root.column) :=
    hLeftward.trans_le (Nat.le_add_right _ _)
  refine ⟨?_, hParentRead, ?_, ?_⟩
  · rw [hUpperFixed]
    simp [copyEdge, hSource, hNonzero, leftOf, hStored,
      show (Frame.ref parent).column < p.root.column from hFixed,
      Nat.not_le_of_gt hDestination]
  · rw [hStationary]
    exact Frame.P_height_le hNormal.toOrdered hParent
  · simpa only [hStationary] using hSourceB

private theorem frame_upper_of_refs {F : Frame} {before after : F.Node} {column index : Nat}
    (hBefore : Frame.ref before = ⟨column, index⟩)
    (hAfter : Frame.ref after = ⟨column, index + 1⟩) : F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hBefore hAfter
  have hc : d = c := Fin.ext (hAfter.1.trans hBefore.1.symm)
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, by omega⟩

section ActualContour

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
  (s : DynamicBlockState p block start references next ambient)
  (d : ColumnCopyData ambient p.marked references next
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
  {column : Column} {index : Nat} {lower upper : Cell}
  (pair : ExecutedSegmentPair d index lower upper)
  {pathIndex : Nat}
  (execution : ContourAdjacentExecution ambient next (d.bucket.map Ref.index)
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column d.sources
    (d.marker_data pair.marker pair.member).current.row
    (d.marker_data pair.marker pair.member).targetCell.row
    pair.marker.index pair.path pathIndex pair.originalLower pair.originalUpper)

include s in
private theorem actual_source_pair :
    ∃ child sourceUpper : (Frame.ofMountain p.reduced).Node,
      Frame.ref child = ⟨next, pair.marker.index + pathIndex + 1⟩ ∧
      Frame.ref sourceUpper = ⟨next, pair.marker.index + pathIndex + 2⟩ ∧
      (Frame.ofMountain p.reduced).cell child = execution.lower ∧
      (Frame.ofMountain p.reduced).cell sourceUpper = execution.upper ∧
      Frame.Real child ∧ (Frame.ofMountain p.reduced).upper child = some sourceUpper := by
  have hSpec := p.marker_iff.mp (show BucketMem p.marked next ⟨next, 0⟩ from d.phantom_marker)
  obtain ⟨_, phantomNodes, hPhantomColumn, _⟩ := hSpec.2.2.1
  have hNext : next < p.reduced.size := (Array.getElem?_eq_some_iff.mp hPhantomColumn).1
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  obtain ⟨child, hChildRef, hChildCell⟩ := Canonical.frame_node_of_cellAt (execution.lower_cellAt hSource)
  obtain ⟨sourceUpper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt (execution.upper_cellAt hSource)
  have hChildIndex : child.2.val = pair.marker.index + pathIndex + 1 := congrArg Ref.index hChildRef
  exact ⟨child, sourceUpper, hChildRef, hUpperRef, hChildCell, hUpperCell,
    by change 0 < child.2.val; omega,
    frame_upper_of_refs hChildRef (by simpa only [Nat.add_assoc] using hUpperRef)⟩

variable
  (hRun : copyColumn ambient p.marked references next
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
  (hLowerRead : column[index]? = some lower)
  (hUpperRead : column[index + 1]? = some upper)

include s hRun hLowerRead hUpperRead

omit s in
private theorem returned_from_actual_copy {requested : Row} {source : Ref}
    {candidate : Cell} {parentRef : Ref} {parentCell : Cell}
    (hExpected : copyEdge ambient source (block * (p.reduced.size - 1 - p.root.column))
      p.root.column requested = .ok candidate)
    (hActual : copyEdge ambient source (block * (p.reduced.size - 1 - p.root.column))
      p.root.column requested = .ok pair.originalUpper)
    (hLeft : candidate.left = some parentRef)
    (hRead : Canonical.cellAt ambient parentRef = .ok parentCell)
    (hBound : parentCell.row ≤ lower.row) (hB : candidate.row = Row.B lower.row parentCell.row) :
    ReturnedContourEdge ambient column index lower upper := by
  have he : candidate = pair.originalUpper := Except.ok.inj (hExpected.symm.trans hActual)
  have hOutputLeft : upper.left = some parentRef := pair.upper_shape.2.symm.trans (he ▸ hLeft)
  obtain ⟨actualColumn, hActualRun, _, hValid, _, _⟩ := d.copyColumn_valid
  have hSame : actualColumn = column := Except.ok.inj (hActualRun.symm.trans hRun)
  subst actualColumn
  have hLeftward := (hValid.stored_valid _ _ _ hUpperRead hOutputLeft).1
  exact ⟨parentRef, parentCell,
    cellAt_ok_iff.mpr ⟨column, by simp, hLowerRead⟩,
    cellAt_ok_iff.mpr ⟨column, by simp, hUpperRead⟩,
    hOutputLeft, hLeftward, (cellAt_push_left hLeftward).trans hRead,
    hBound, pair.upper_shape.1.symm.trans (he ▸ hB)⟩

/-- The fixed-column stationary case on actual finished contour nodes.
The concrete old stored reference determines the source father through
source Normal; no source P or successful copy premise is supplied. -/
theorem DynamicBlockState.stationary_contour_fixed_geometry
    (hStationary : execution.lower.row = lower.row)
    {oldParentRef : Ref} (hOldLeft : execution.upper.left = some oldParentRef)
    (hFixed : oldParentRef.column < p.root.column) :
    ReturnedContourEdge ambient column index lower upper := by
  obtain ⟨child, sourceUpper, hChildRef, hUpperRef, hChildCell, hUpperCell, hReal, hSourceUpper⟩ :=
    actual_source_pair s d pair execution
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨parent, hParent, _, _, hStored⟩ := hNormal.upper_step child sourceUpper hReal hSourceUpper
  have hStored' : execution.upper.left = some (Frame.ref parent) := by
    simpa only [hUpperCell] using hStored
  have hParentRef : Frame.ref parent = oldParentRef :=
    Option.some.inj (hStored'.symm.trans hOldLeft)
  have hRootLow : (d.marker_data pair.marker pair.member).current.row ≤
      (Frame.ofMountain p.reduced).height child := by
    simpa only [Frame.height, hChildCell] using execution.root_lower
  have hLowerRow : lower.row = (Frame.ofMountain p.reduced).height child := by
    simpa only [Frame.height, hChildCell] using hStationary.symm
  have hLiftFixed : Row.lift (d.marker_data pair.marker pair.member).current.row
      (d.marker_data pair.marker pair.member).targetCell.row
      ((Frame.ofMountain p.reduced).height child) = (Frame.ofMountain p.reduced).height child := by
    simpa only [Frame.height, hChildCell] using
      execution.lower_row.symm.trans (pair.lower_shape.1.trans hStationary.symm)
  obtain ⟨hExpected, hRead, hBound, hB⟩ := s.copyEdge_stationary_fixed_parent hRootLow hLiftFixed
    hParent hSourceUpper (by change (Frame.ref parent).column < p.root.column; rw [hParentRef]; exact hFixed)
  rw [hLiftFixed] at hBound hB
  have hActual : copyEdge ambient (Frame.ref sourceUpper)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row
        ((Frame.ofMountain p.reduced).height sourceUpper)) = .ok pair.originalUpper := by
    simpa only [hUpperRef, Frame.height, hUpperCell] using execution.upper_copy
  apply returned_from_actual_copy d pair hRun hLowerRead hUpperRead hExpected hActual rfl hRead
  · simpa only [hLowerRow, Frame.height] using hBound
  · simpa only [hLowerRow, Frame.height] using hB

/-- Active-parent geometry on actual contour output. Its lower source
node may be above the cap and unchanged while its father is lifted. The
source father is identified solely by the actual source upper's stored
reference; source P and both source-node reads are derived internally. -/
theorem DynamicBlockState.active_contour_execution_geometry
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {sourceIndex : Nat}
    (a : ActualRootInterval p start ambient references sourceIndex
      (d.marker_data pair.marker pair.member).current.row)
    (hTarget : a.target.row = (d.marker_data pair.marker pair.member).targetCell.row)
    {sourceParent : (Frame.ofMountain p.reduced).Node}
    (hStored : execution.upper.left = some (Frame.ref sourceParent))
    (hParentInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump (d.marker_data pair.marker pair.member).current.row a.degree) sourceParent)
    (hParentAbove : (d.marker_data pair.marker pair.member).current.row <
      (Frame.ofMountain p.reduced).height sourceParent) :
    ReturnedContourEdge ambient column index lower upper := by
  obtain ⟨child, sourceUpper, hChildRef, hUpperRef, hChildCell, hUpperCell, hReal, hSourceUpper⟩ :=
    actual_source_pair s d pair execution
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨parent, hParent, _, _, hOldStored⟩ := hNormal.upper_step child sourceUpper hReal hSourceUpper
  have hStored' : execution.upper.left = some (Frame.ref parent) := by
    simpa only [hUpperCell] using hOldStored
  have hParentRef : Frame.ref parent = Frame.ref sourceParent :=
    Option.some.inj (hStored'.symm.trans hStored)
  have hParentEq : parent = sourceParent := Executable.ref_injective _ hParentRef
  subst parent
  have hChildColumn : child.1.val = next := congrArg Ref.column hChildRef
  obtain ⟨candidate, parentRef, parentCell, hExpected, _, hLeft, _, hRead, _, hBound, hB⟩ :=
    s.copyEdge_active_parent history hLast a hParentInside hParentAbove hParent hChildColumn hSourceUpper
  have hActual : copyEdge ambient (Frame.ref sourceUpper)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      (Row.lift (d.marker_data pair.marker pair.member).current.row a.target.row
        ((Frame.ofMountain p.reduced).height sourceUpper)) = .ok pair.originalUpper := by
    simpa only [hUpperRef, Frame.height, hUpperCell, hTarget] using execution.upper_copy
  have hLowerRow : lower.row = Row.lift (d.marker_data pair.marker pair.member).current.row a.target.row
      ((Frame.ofMountain p.reduced).height child) := by
    simpa only [Frame.height, hChildCell, hTarget] using pair.lower_shape.1.symm.trans execution.lower_row
  exact returned_from_actual_copy d pair hRun hLowerRead hUpperRead hExpected hActual hLeft hRead
    (by simpa only [hLowerRow] using hBound) (by simpa only [hLowerRow] using hB)

end ActualContour

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_active_parent
#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_stationary_fixed_parent
#print axioms OmegaY.Expansion.DynamicBlockState.stationary_contour_fixed_geometry
#print axioms OmegaY.Expansion.DynamicBlockState.active_contour_execution_geometry
