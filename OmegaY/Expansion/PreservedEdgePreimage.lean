/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedEdgePreimage.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PreservedMountainKeys

/-! Every actual edge in a retained complete column has a real source
edge, including its upper and parent. This is inverse edge provenance,
not an assumed correspondence between node positions. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

private theorem storedEdge_eq_of_nodes {F : Frame} {left right : RealStoredEdge F}
    (hLower : left.lower = right.lower) (hUpper : left.upper = right.upper)
    (hParent : left.parent = right.parent) : left = right := by
  cases left
  cases right
  cases hLower
  cases hUpper
  cases hParent
  rfl

theorem PreservesColumns.storedEdge_preimage {before after : Mountain}
    (preserved : PreservesColumns before after)
    (hAfter : (Frame.ofMountain after).Ordered)
    (edge : RealStoredEdge (Frame.ofMountain after))
    (hColumn : edge.lower.1.val < before.size) :
    ∃ oldEdge : RealStoredEdge (Frame.ofMountain before),
      preserved.storedEdge oldEdge = edge := by
  have hUpperColumn : edge.upper.1.val < before.size :=
    (congrArg Fin.val (upper_spec edge.upper_eq).1).trans_lt hColumn
  have hParentColumn : edge.parent.1.val < before.size :=
    (rawParent_column_lt hAfter edge.parent_eq).trans hColumn
  have hLowerRead := (preserved.cellAt hColumn).symm.trans (Canonical.cellAt_of_frame_node after edge.lower)
  have hUpperRead := (preserved.cellAt hUpperColumn).symm.trans (Canonical.cellAt_of_frame_node after edge.upper)
  have hParentRead := (preserved.cellAt hParentColumn).symm.trans (Canonical.cellAt_of_frame_node after edge.parent)
  obtain ⟨lower, hLowerRef, _⟩ := Canonical.frame_node_of_cellAt hLowerRead
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  obtain ⟨parent, hParentRef, _⟩ := Canonical.frame_node_of_cellAt hParentRead
  have hReal : Real lower := by
    have hi : lower.2.val = edge.lower.2.val := congrArg Ref.index hLowerRef
    change 0 < lower.2.val
    rw [hi]
    exact edge.lower_real
  have hUpper : (Frame.ofMountain before).upper lower = some upper :=
    upper_of_refs hLowerRef (hUpperRef.trans
      (congrArg₂ Ref.mk (congrArg Fin.val (upper_spec edge.upper_eq).1) (upper_spec edge.upper_eq).2))
  have hActualLeft : ((Frame.ofMountain after).cell edge.upper).left = some (Frame.ref edge.parent) := by
    obtain ⟨next, hNext, hLeft⟩ := rawParent_spec edge.parent_eq
    have he : next = edge.upper := Option.some.inj (hNext.symm.trans edge.upper_eq)
    exact he ▸ hLeft
  have hParent : (Frame.ofMountain before).rawParent lower = some parent :=
    rawParent_eq_of_upper_left hUpper (by simpa only [hUpperCell, hParentRef] using hActualLeft)
  let oldEdge : RealStoredEdge (Frame.ofMountain before) :=
    ⟨lower, upper, parent, hReal, hUpper, hParent⟩
  refine ⟨oldEdge, storedEdge_eq_of_nodes ?_ ?_ ?_⟩
  · exact Executable.ref_injective _ ((preserved.mapNode_ref lower).trans hLowerRef)
  · exact Executable.ref_injective _ ((preserved.mapNode_ref upper).trans hUpperRef)
  · exact Executable.ref_injective _ ((preserved.mapNode_ref parent).trans hParentRef)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.storedEdge_preimage
