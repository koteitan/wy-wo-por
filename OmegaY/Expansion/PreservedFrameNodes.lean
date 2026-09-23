/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedFrameNodes.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectivePaths
import OmegaY.Expansion.SourceFatherBound

/-!
# Typed nodes and stored edges in a preserved complete prefix

The map is recovered from actual preserved cell reads. It preserves exact
references, full cells, consecutive uppers and stored parents. No numerical
parent preservation is claimed for an arbitrary noncanonical extension.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem preserved_node_exists {before after : Mountain}
    (h : PreservesColumns before after) (node : (Frame.ofMountain before).Node) :
    ∃ mapped : (Frame.ofMountain after).Node,
      Frame.ref mapped = Frame.ref node ∧
      (Frame.ofMountain after).cell mapped = (Frame.ofMountain before).cell node := by
  apply Canonical.frame_node_of_cellAt
  exact (cellAt_eq_of_column_eq (h node.1.val node.1.isLt)).trans
    (Canonical.cellAt_of_frame_node before node)

noncomputable def PreservesColumns.mapNode {before after : Mountain}
    (h : PreservesColumns before after) (node : (Frame.ofMountain before).Node) :
    (Frame.ofMountain after).Node := Classical.choose (preserved_node_exists h node)

theorem PreservesColumns.mapNode_ref {before after : Mountain}
    (h : PreservesColumns before after) (node : (Frame.ofMountain before).Node) :
    Frame.ref (h.mapNode node) = Frame.ref node :=
  (Classical.choose_spec (preserved_node_exists h node)).1

theorem PreservesColumns.mapNode_cell {before after : Mountain}
    (h : PreservesColumns before after) (node : (Frame.ofMountain before).Node) :
    (Frame.ofMountain after).cell (h.mapNode node) = (Frame.ofMountain before).cell node :=
  (Classical.choose_spec (preserved_node_exists h node)).2

theorem PreservesColumns.mapNode_column {before after : Mountain}
    (h : PreservesColumns before after) (node : (Frame.ofMountain before).Node) :
    (h.mapNode node).1.val = node.1.val := congrArg Ref.column (h.mapNode_ref node)

theorem PreservesColumns.mapNode_index {before after : Mountain}
    (h : PreservesColumns before after) (node : (Frame.ofMountain before).Node) :
    (h.mapNode node).2.val = node.2.val := congrArg Ref.index (h.mapNode_ref node)

theorem PreservesColumns.mapNode_height {before after : Mountain}
    (h : PreservesColumns before after) (node : (Frame.ofMountain before).Node) :
    (Frame.ofMountain after).height (h.mapNode node) = (Frame.ofMountain before).height node :=
  congrArg Cell.row (h.mapNode_cell node)

theorem PreservesColumns.mapNode_real {before after : Mountain}
    (h : PreservesColumns before after) {node : (Frame.ofMountain before).Node}
    (hReal : Frame.Real node) : Frame.Real (h.mapNode node) := by
  change 0 < (h.mapNode node).2.val
  rw [h.mapNode_index]
  exact hReal

theorem PreservesColumns.mapNode_upper {before after : Mountain}
    (h : PreservesColumns before after) {node upper : (Frame.ofMountain before).Node}
    (hUpper : (Frame.ofMountain before).upper node = some upper) :
    (Frame.ofMountain after).upper (h.mapNode node) = some (h.mapNode upper) := by
  apply Frame.upper_of_refs (h.mapNode_ref node)
  rw [h.mapNode_ref upper]
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩

theorem PreservesColumns.mapNode_rawParent {before after : Mountain}
    (h : PreservesColumns before after) {node parent : (Frame.ofMountain before).Node}
    (hParent : (Frame.ofMountain before).rawParent node = some parent) :
    (Frame.ofMountain after).rawParent (h.mapNode node) = some (h.mapNode parent) :=
  ((RawRefEdge.of_rawParent hParent).preserve h).rawParent (h.mapNode_ref node) (h.mapNode_ref parent)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.mapNode_ref
#print axioms OmegaY.Expansion.PreservesColumns.mapNode_cell
#print axioms OmegaY.Expansion.PreservesColumns.mapNode_upper
#print axioms OmegaY.Expansion.PreservesColumns.mapNode_rawParent
