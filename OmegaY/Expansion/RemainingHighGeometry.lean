/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RemainingHighGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighEdge
import OmegaY.Expansion.ActualRemainingRaw

/-!
# High-parent geometry for actual remaining contour and seam edges

The successful individual copy comes from the returned column's execution
certificate. Determinism identifies it with the independently proved high
copyEdge result, and shape preservation places its stored leg and B row
at the actual returned indices. No output numerical parent is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem node_eq_of_same_column_height {F : Frame} (hOrdered : F.Ordered)
    {u v : F.Node} (hColumn : u.1 = v.1) (hHeight : F.height u = F.height v) : u = v := by
  cases u with
  | mk c i =>
    cases v with
    | mk d j =>
      dsimp only at hColumn
      subst d
      have hi : i = j := (hOrdered.rows_strict c).injective hHeight
      cases hi
      rfl

/-- A stationary source lower row identifies one actual node in its
strictly ordered column. Thus its source P father is also unique. -/
private theorem source_pair_parent_high {front : List Nat} {last : Nat}
    {p : Preparation front last} {next sourceIndex : Nat} {sourceLower sourceUpper lower : Cell}
    (source : SourceNumericalPair p.reduced next sourceIndex sourceLower sourceUpper)
    (hStationary : sourceLower.row = lower.row)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent) :
    p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source.parentNode := by
  have hSourceColumn : source.lowerNode.1.val = next := congrArg Ref.column source.lower_ref
  have hSourceRow : (Frame.ofMountain p.reduced).height source.lowerNode = lower.row := by
    simpa only [Frame.height, source.lower_cell] using hStationary
  have he : source.lowerNode = child := node_eq_of_same_column_height p.reduced_valid.toOrdered
    (Fin.ext (hSourceColumn.trans hChildColumn.symm)) (hSourceRow.trans hChildRow.symm)
  have hSourceParent := source.source_parent
  rw [he] at hSourceParent
  have hp : source.parentNode = parent := Option.some.inj (hSourceParent.symm.trans hParent)
  simpa only [hp] using hHigh

/-- Common returned-output interface for both contour interiors and
segment seams. The actual candidate call and its preserved output shape
are provenance data; the stored parent's existence, bound and B equation
are derived from the high-source-edge theorem. -/
theorem DynamicBlockState.returned_high_source_copy_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    {child parent sourceUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hSourceUpper : (Frame.ofMountain p.reduced).upper child = some sourceUpper)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent)
    {originalUpper : Cell}
    (hActual : copyEdge ambient (Frame.ref sourceUpper)
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column
      ((Frame.ofMountain p.reduced).height sourceUpper) = .ok originalUpper)
    {column : Column} {index : Nat} {lower upper : Cell}
    (hLowerRow : lower.row = (Frame.ofMountain p.reduced).height child)
    (hUpperShape : originalUpper.row = upper.row ∧ originalUpper.left = upper.left)
    (hLowerRead : column[index]? = some lower)
    (hUpperRead : column[index + 1]? = some upper) :
    ReturnedContourEdge ambient column index lower upper := by
  obtain ⟨copied, parentRef, parentCell, hExpected, _, _, hLeft, _, hBefore,
      hRead, _, hBound, hB⟩ :=
    s.copyEdge_high_parent history hLast hStartRun hParent hChildColumn hSourceUpper hHigh
  have he : copied = originalUpper := Except.ok.inj (hExpected.symm.trans hActual)
  have hOutputLeft : upper.left = some parentRef := hUpperShape.2.symm.trans (he ▸ hLeft)
  have hOutputB : upper.row = Row.B lower.row parentCell.row := by
    rw [hLowerRow]
    exact hUpperShape.1.symm.trans (he ▸ hB)
  exact ⟨parentRef, parentCell,
    cellAt_ok_iff.mpr ⟨column, by simp, hLowerRead⟩,
    cellAt_ok_iff.mpr ⟨column, by simp, hUpperRead⟩,
    hOutputLeft, hBefore, (cellAt_push_left hBefore).trans hRead,
    hLowerRow ▸ hBound, hOutputB⟩

/-- Every remaining actual contour or seam edge whose stationary source
parent is high has the required raw output geometry. The independent
source node at the output lower row is identified with the one recovered
by the execution classification; no output P equation is an input. -/
theorem DynamicBlockState.remaining_high_geometry
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
    {column : Column} {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper)
    (hLowerRead : column[index]? = some lower)
    (hUpperRead : column[index + 1]? = some upper)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next)
    (hChildRow : (Frame.ofMountain p.reduced).height child = lower.row)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent) :
    CopiedRawAt ambient column lower upper := by
  cases origin with
  | contour_inside pair pathIndex _ _ _ execution source hStationary _ _ hCopy =>
    have hSourceHigh := source_pair_parent_high source hStationary hParent hChildColumn hChildRow hHigh
    have hActual : copyEdge ambient (Frame.ref source.upperNode)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        ((Frame.ofMountain p.reduced).height source.upperNode) = .ok pair.originalUpper := by
      simpa only [Frame.height, source.upper_cell] using hCopy
    have hLowerRow : lower.row = (Frame.ofMountain p.reduced).height source.lowerNode := by
      simpa only [Frame.height, source.lower_cell] using hStationary.symm
    exact (s.returned_high_source_copy_geometry history hLast hStartRun source.source_parent
      (congrArg Ref.column source.lower_ref) source.source_upper hSourceHigh hActual hLowerRow
      pair.upper_shape hLowerRead hUpperRead).raw_geometry
  | cross_segment seam sourceLower _ _ source hStationary _ _ hCopy =>
    have hSourceHigh := source_pair_parent_high source hStationary hParent hChildColumn hChildRow hHigh
    have hActual : copyEdge ambient (Frame.ref source.upperNode)
        (block * (p.reduced.size - 1 - p.root.column)) p.root.column
        ((Frame.ofMountain p.reduced).height source.upperNode) = .ok seam.originalUpper := by
      simpa only [Frame.height, source.upper_cell] using hCopy
    have hLowerRow : lower.row = (Frame.ofMountain p.reduced).height source.lowerNode := by
      simpa only [Frame.height, source.lower_cell] using hStationary.symm
    exact (s.returned_high_source_copy_geometry history hLast hStartRun source.source_parent
      (congrArg Ref.column source.lower_ref) source.source_upper hSourceHigh hActual hLowerRow
      seam.upper_shape hLowerRead hUpperRead).raw_geometry

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.returned_high_source_copy_geometry
#print axioms OmegaY.Expansion.DynamicBlockState.remaining_high_geometry
