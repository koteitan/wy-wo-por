/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowBoundaryValue.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualIteratedBoundaryDepth
import OmegaY.Expansion.BlockEquations

/-!
# Numerical lower bounds for actual iterated low-root references

Positive backfill makes every real stored-parent step decrease values.
The actual all-block boundary path therefore puts its selected node above
the unchanged original low root in value. This is a boundary comparison,
not a source-to-copy last-blocker comparison or expansion descent theorem.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem RawRefPath.value_le {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {child parent : Ref} (path : RawRefPath mountain child parent)
    {u p : (Frame.ofMountain mountain).Node} (hU : Frame.ref u = child)
    (hP : Frame.ref p = parent) (hReal : Real u) :
    (Frame.ofMountain mountain).value p ≤ (Frame.ofMountain mountain).value u := by
  induction path generalizing u with
  | refl ref =>
      have he : u = p := Executable.ref_injective _ (hU.trans hP.symm)
      exact he ▸ le_rfl
  | @cons child next parent edge tail ih =>
      have edgeRead := edge
      obtain ⟨_, _, _, _, _, _, hRead⟩ := edgeRead
      obtain ⟨q, hQRef, _⟩ := Canonical.frame_node_of_cellAt hRead
      have hRaw := edge.rawParent hU hQRef
      obtain ⟨hQReal, hSmall⟩ := hSums.rawParent_value_lt hValid hReal hRaw
      exact (ih hQRef hP hQReal).trans hSmall.le

theorem RawRefPath.value_lt_of_ne {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {child parent : Ref} (path : RawRefPath mountain child parent)
    {u p : (Frame.ofMountain mountain).Node} (hU : Frame.ref u = child)
    (hP : Frame.ref p = parent) (hReal : Real u) (hDistinct : child ≠ parent) :
    (Frame.ofMountain mountain).value p < (Frame.ofMountain mountain).value u := by
  cases path with
  | refl ref => exact False.elim (hDistinct rfl)
  | @cons child next parent edge tail =>
      have edgeRead := edge
      obtain ⟨_, _, _, _, _, _, hRead⟩ := edgeRead
      obtain ⟨q, hQRef, _⟩ := Canonical.frame_node_of_cellAt hRead
      obtain ⟨hQReal, hSmall⟩ := hSums.rawParent_value_lt hValid hReal (edge.rawParent hU hQRef)
      exact (tail.value_le hSums hValid hQRef hP hQReal).trans_lt hSmall

theorem Preparation.blocks_low_boundary_value
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper) :
    ∃ packet : LowBoundaryEventDepth p result root rootUpper,
      (Frame.ofMountain p.initial).value root < (Frame.ofMountain result).value packet.selected := by
  obtain ⟨packet⟩ := p.blocks_low_boundary_event_depth hLast hRun hRootReal hRootColumn hBefore hRootUpper
  obtain ⟨actual, hActual, ready, hSums, _⟩ := p.blocks_equations hLast copies
  have he : actual = result := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  have hPath := p.blocks_low_selected_path hLast hRun hRootReal hRootColumn hBefore hRootUpper
    packet.selected_below
  have hReal : Real packet.selected := by
    rw [← packet.selected_frontier]
    exact (eventFrontier_spec packet.valid.toOrdered packet.event packet.selected.1).2.1
  have hReducedSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hReducedSize
  have hSize : p.reduced.size ≤ result.size := ready.base_preserved.size_le
  have hDistinct : Frame.ref packet.selected ≠ Frame.ref root := by
    intro hEq
    have hColumn := congrArg Ref.column hEq
    change packet.selected.1.val = root.1.val at hColumn
    rw [packet.selected_column, hRootColumn] at hColumn
    have hRootLast := p.root_before_last
    omega
  have hValue := hPath.value_lt_of_ne hSums packet.valid rfl packet.root_reference hReal hDistinct
  refine ⟨packet, ?_⟩
  change ((Frame.ofMountain p.initial).cell root).value < _
  rw [← packet.root_cell]
  exact hValue

end OmegaY.Expansion

#print axioms OmegaY.Expansion.RawRefPath.value_le
#print axioms OmegaY.Expansion.RawRefPath.value_lt_of_ne
#print axioms OmegaY.Expansion.Preparation.blocks_low_boundary_value
