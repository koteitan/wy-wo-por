/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RaisedContourGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ContourExecutionAt
import OmegaY.Expansion.ActualMarkerTransport
import OmegaY.Expansion.ActualIntervalEdge

/-!
# Stored geometry of actually raised contour-interior edges

The source nodes, their numerical father, their root-interval membership,
and the executable copied edge are recovered from actual contour reads.
Only a strict rise of the actual lower row selects the raised case. No
normality, numerical-parent equation, or desired B equation for the output
is an input. The result concerns stored geometry, not output first-smaller
selection.
-/

namespace OmegaY.Expansion

open Canonical Geometry

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

/-- The interval's actual column split also preserves the lower-endpoint
bound on the parent row. In the fixed branch the source parent is below
the root; in the moved branch both rows share the same monotone lift. -/
theorem ActualRootInterval.interval_parent_row_le
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {index : Nat} {sourceRow : Row}
    (a : ActualRootInterval p start ambient references index sourceRow)
    (hRaised : sourceRow < a.target.row)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hChild : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump sourceRow a.degree) child)
    (hParent : (Frame.ofMountain p.reduced).P child = some parent) :
    (Frame.ofMountain p.reduced).intervalParentRow a.root a.target.row parent ≤
      Row.lift sourceRow a.target.row ((Frame.ofMountain p.reduced).height child) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hInside : Frame.RootInterval (Frame.ofMountain p.reduced) a.root
      (Row.bump ((Frame.ofMountain p.reduced).height a.root) a.degree) child := by
    simpa only [a.root_row] using hChild
  have hBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper a.root = some upper →
      Row.bump ((Frame.ofMountain p.reduced).height a.root) a.degree ≤
        (Frame.ofMountain p.reduced).height upper := by
    simpa only [a.root_row] using a.root_upper_barrier
  rcases Frame.root_interval_parent_bump hNormal a.root_real (a.raised_degree hRaised)
      hBarrier hParent hInside with hi | ⟨hb, _⟩
  · have hc := Frame.RootCone.column_le hNormal.toOrdered hi.1
    rw [Frame.intervalParentRow, if_neg (Nat.not_lt_of_ge hc), a.root_row]
    exact Row.lift_monotone (by simpa only [a.root_row] using hi.2.1)
      (Frame.P_height_le hNormal.toOrdered hParent)
  · rw [Frame.intervalParentRow, if_pos hb.1]
    have hLow : sourceRow ≤ (Frame.ofMountain p.reduced).height child := by
      simpa only [a.root_row] using hChild.2.1
    exact (Frame.P_height_le hNormal.toOrdered hParent).trans
      (Row.lift_ge_source a.target_lower hLow)

/-- An actual adjacent output pair and its actual stored father. This
contains the parent-row bound as well as B; it does not assert that the
output numerical first-smaller search has yet been identified. -/
def ReturnedContourEdge (ambient : Mountain) (column : Column) (index : Nat)
    (lower upper : Cell) : Prop :=
  ∃ (parentRef : Ref) (parent : Cell),
    Canonical.cellAt (ambient.push column) ⟨ambient.size, index⟩ = .ok lower ∧
    Canonical.cellAt (ambient.push column) ⟨ambient.size, index + 1⟩ = .ok upper ∧
    upper.left = some parentRef ∧ parentRef.column < ambient.size ∧
    Canonical.cellAt (ambient.push column) parentRef = .ok parent ∧
    parent.row ≤ lower.row ∧ upper.row = Row.B lower.row parent.row

section ActualContour

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (d : ColumnCopyData ambient p.marked references next
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column)
  {column : Column} {index : Nat} {lower upper : Cell}
  (pair : ExecutedSegmentPair d index lower upper)
  (hRun : copyColumn ambient p.marked references next
    (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
  (hLowerRead : column[index]? = some lower)
  (hUpperRead : column[index + 1]? = some upper)

include s history hLast hRun hLowerRead hUpperRead

/-- Execution-certificate interface. The certificate contains actual
source reads and successful individual calls, all recovered by the public
contour-inside wrapper below. No source pair or cone hypothesis is added. -/
theorem DynamicBlockState.raised_contour_execution_geometry {pathIndex : Nat}
    (execution : ContourAdjacentExecution ambient next (d.bucket.map Ref.index)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column d.sources
      (d.marker_data pair.marker pair.member).current.row
      (d.marker_data pair.marker pair.member).targetCell.row
      pair.marker.index pair.path pathIndex pair.originalLower pair.originalUpper)
    (hRaisedLower : execution.lower.row < lower.row) :
    ReturnedContourEdge ambient column index lower upper := by
  let md := d.marker_data pair.marker pair.member
  have hSpec := p.marker_iff.mp (show BucketMem p.marked next ⟨next, 0⟩ from d.phantom_marker)
  obtain ⟨phantom, phantomNodes, hPhantomColumn, _⟩ := hSpec.2.2.1
  have hNext : next < p.reduced.size := (Array.getElem?_eq_some_iff.mp hPhantomColumn).1
  have hSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  obtain ⟨child, hChildRef, hChildCell⟩ := Canonical.frame_node_of_cellAt (execution.lower_cellAt hSource)
  obtain ⟨sourceUpper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt (execution.upper_cellAt hSource)
  have hChildColumn : child.1.val = next := congrArg Ref.column hChildRef
  have hChildIndex : child.2.val = pair.marker.index + pathIndex + 1 := congrArg Ref.index hChildRef
  have hChildReal : Frame.Real child := by change 0 < child.2.val; omega
  have hSourceUpper : (Frame.ofMountain p.reduced).upper child = some sourceUpper :=
    frame_upper_of_refs hChildRef (by simpa only [Nat.add_assoc] using hUpperRef)
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨parent, hParent, _⟩ := hNormal.upper_step child sourceUpper hChildReal hSourceUpper
  have hLowerRow : lower.row = Row.lift md.current.row md.targetCell.row
      ((Frame.ofMountain p.reduced).height child) := by
    simpa only [Frame.height, hChildCell] using pair.lower_shape.1.symm.trans execution.lower_row
  have hChildRaised : (Frame.ofMountain p.reduced).height child < lower.row := by
    simpa only [Frame.height, hChildCell] using hRaisedLower
  rcases s.marker_source_transport hLast d pair.member hChildColumn (by omega) with
    ⟨_, hFixed⟩ | ⟨rootIndex, a, hTarget, hRaised, hInterval | ⟨_, hFixed⟩⟩
  · exact False.elim ((ne_of_lt hChildRaised) (hLowerRow.trans hFixed).symm)
  · have hCopy : copyEdge ambient (Frame.ref sourceUpper)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        (Row.lift md.current.row a.target.row ((Frame.ofMountain p.reduced).height sourceUpper)) =
          .ok pair.originalUpper := by
      simpa only [hUpperRef, Frame.height, hUpperCell, hTarget] using execution.upper_copy
    have hLowerTarget : lower.row = Row.lift md.current.row a.target.row
        ((Frame.ofMountain p.reduced).height child) := by simpa only [hTarget] using hLowerRow
    obtain ⟨parentRef, actualParent, hLow, hHigh, hLeft, _, hRead, hParentRow, hB⟩ :=
      s.returned_interval_edge history hLast a hRaised hInterval hParent hChildColumn hSourceUpper
        hLowerRead hUpperRead hCopy pair.upper_shape hLowerTarget
    have hParentBound : actualParent.row ≤ lower.row := by
      rw [hParentRow, hLowerTarget]
      exact a.interval_parent_row_le hRaised hInterval hParent
    obtain ⟨actualColumn, hActualRun, _, hValid, _, _⟩ := d.copyColumn_valid
    have hSame : actualColumn = column := Except.ok.inj (hActualRun.symm.trans hRun)
    subst actualColumn
    exact ⟨parentRef, actualParent, hLow, hHigh, hLeft,
      (hValid.stored_valid _ _ _ hUpperRead hLeft).1, hRead, hParentBound, hB⟩
  · exact False.elim ((ne_of_lt hChildRaised) (hLowerRow.trans hFixed).symm)

/-- Actual contour-inside provenance supplies the execution certificate.
Its actual source lower row is the only row in the strict-rise condition;
all source parent, interval, and individual-copy facts are conclusions. -/
theorem DynamicBlockState.raised_contour_inside_geometry {pathIndex : Nat}
    (hPathLower : pair.path[pathIndex]? = some pair.originalLower)
    (hPathUpper : pair.path[pathIndex + 1]? = some pair.originalUpper) :
    ∃ execution : ContourAdjacentExecution ambient next (d.bucket.map Ref.index)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column d.sources
        (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row
        pair.marker.index pair.path pathIndex pair.originalLower pair.originalUpper,
      lower.row = Row.lift (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row execution.lower.row ∧
      upper.row = Row.lift (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row execution.upper.row ∧
      (execution.lower.row < lower.row → ReturnedContourEdge ambient column index lower upper) := by
  obtain ⟨execution, hLow, hHigh, _, _⟩ := pair.contour_inside_source hPathLower hPathUpper
  exact ⟨execution, hLow, hHigh, s.raised_contour_execution_geometry history hLast d pair
    hRun hLowerRead hUpperRead execution⟩

end ActualContour

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualRootInterval.interval_parent_row_le
#print axioms OmegaY.Expansion.DynamicBlockState.raised_contour_execution_geometry
#print axioms OmegaY.Expansion.DynamicBlockState.raised_contour_inside_geometry
