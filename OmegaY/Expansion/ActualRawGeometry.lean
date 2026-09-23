/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRawGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRemainingRaw
import OmegaY.Expansion.NonrootParentGeometry
import OmegaY.Expansion.RemainingRootParent

/-! Recover the actual source parent of each exact residual before
splitting on its column. Numerical parents refer to the frozen source,
never to an as-yet unverified search in the copied graph. -/

namespace OmegaY.Expansion

open Canonical Geometry

theorem RemainingMovedStationaryOrigin.source_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {ambient : Mountain} {references : List Ref} {sourceColumn shift : Nat}
    {d : ColumnCopyData ambient p.marked references sourceColumn shift p.root.column}
    {index : Nat} {lower upper : Cell}
    (origin : RemainingMovedStationaryOrigin p d index lower upper) :
    ∃ child parent : (Frame.ofMountain p.reduced).Node,
      (Frame.ofMountain p.reduced).P child = some parent ∧
      child.1.val = sourceColumn ∧ (Frame.ofMountain p.reduced).height child = lower.row ∧
      p.root.column ≤ parent.1.val := by
  cases origin with
  | contour_inside pair pathIndex _ _ _ execution source hStationary _ hMoved _ =>
    exact ⟨source.lowerNode, source.parentNode, source.source_parent,
      congrArg Ref.column source.lower_ref,
      by simpa only [Frame.height, source.lower_cell] using hStationary, hMoved⟩
  | cross_segment seam sourceLower _ _ source hStationary _ hMoved _ =>
    exact ⟨source.lowerNode, source.parentNode, source.source_parent,
      congrArg Ref.column source.lower_ref,
      by simpa only [Frame.height, source.lower_cell] using hStationary, hMoved⟩

/-- Every real adjacency in an actually executed copied column satisfies
the stored-parent row equation. Both the source classification and every
parent-column case are discharged internally; no copied numerical parent
or copied normality is assumed. -/
theorem DynamicBlockState.actual_adjacent_raw_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    (hNext : next < p.reduced.size) {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
    {index : Nat} {lower upper : Cell}
    (hLower : column[index]? = some lower) (hUpper : column[index + 1]? = some upper)
    (hReal : lower.row ≠ 0) : CopiedRawAt ambient column lower upper := by
  rcases s.actual_adjacent_remaining_raw_cases history hLast hNext hRun hLower hUpper hReal with
    hRaw | ⟨d, hSource, _, _, _, origin⟩
  · exact hRaw
  obtain ⟨child, parent, hParent, hChildColumn, hChildRow, hMoved⟩ := origin.source_parent
  rcases eq_or_lt_of_le hMoved with hRoot | hRight
  · exact s.remaining_root_parent_geometry history hLast hStartRun d hSource origin
      hParent hChildColumn hChildRow hRoot.symm hLower hUpper
  · exact s.nonroot_parent_raw_geometry history hLast d origin
      hParent hChildColumn hChildRow hRight hLower hUpper

end OmegaY.Expansion

#print axioms OmegaY.Expansion.RemainingMovedStationaryOrigin.source_parent
#print axioms OmegaY.Expansion.DynamicBlockState.actual_adjacent_raw_geometry
