/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedMountainKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.MountainKeys
import OmegaY.Expansion.PreservedEventDepth

/-!
# Exact multi-root keys in retained complete columns

Adding later columns changes neither an old scale forest nor any of its
actual roots. The old finite edge template is therefore carried by the
literal inclusion of column indices. This supplies the unchanged-edge
part of later key transport; no assertion about newly copied edges is made.
-/

namespace OmegaY.Expansion

universe u

open Canonical Geometry Frame

namespace PreservesColumns

variable {before after : Mountain} (preserved : PreservesColumns before after)

def keyColumn : Fin before.size → Fin after.size :=
  fun column => ⟨column.val, column.isLt.trans_le preserved.size_le⟩

theorem keyColumn_strictMono : StrictMono preserved.keyColumn := by
  intro i j hij
  exact hij

theorem mapNode_scaleParent (hBefore : (Frame.ofMountain before).Ordered)
    (k : Nat) (node : (Frame.ofMountain before).Node) :
    (Frame.ofMountain after).scaleParent k (preserved.mapNode node) =
      ((Frame.ofMountain before).scaleParent k node).map preserved.mapNode := by
  unfold scaleParent
  rw [preserved.mapNode_rawParent_eq hBefore]
  cases hParent : (Frame.ofMountain before).rawParent node with
  | none => rfl
  | some parent =>
      simp only [Option.map_some, Option.bind_some, preserved.mapNode_height]
      split <;> rfl

theorem mapNode_scaleRoot (hBefore : (Frame.ofMountain before).Ordered)
    (hAfter : (Frame.ofMountain after).Ordered)
    (k : Nat) (node : (Frame.ofMountain before).Node) :
    scaleRoot hAfter k (preserved.mapNode node) = preserved.mapNode (scaleRoot hBefore k node) := by
  cases hParent : (Frame.ofMountain before).scaleParent k node with
  | none =>
      have hMapped := preserved.mapNode_scaleParent hBefore k node
      rw [hParent] at hMapped
      rw [scaleRoot_eq_of_none hAfter hMapped, scaleRoot_eq_of_none hBefore hParent]
  | some parent =>
      have hMapped := preserved.mapNode_scaleParent hBefore k node
      rw [hParent] at hMapped
      rw [scaleRoot_eq_of_parent hAfter hMapped, scaleRoot_eq_of_parent hBefore hParent]
      exact mapNode_scaleRoot hBefore hAfter k parent
termination_by node.1.val
decreasing_by exact scaleParent_column_lt hBefore hParent

noncomputable def storedEdge (edge : RealStoredEdge (Frame.ofMountain before)) :
    RealStoredEdge (Frame.ofMountain after) where
  lower := preserved.mapNode edge.lower
  upper := preserved.mapNode edge.upper
  parent := preserved.mapNode edge.parent
  lower_real := preserved.mapNode_real edge.lower_real
  upper_eq := preserved.mapNode_upper edge.upper_eq
  parent_eq := preserved.mapNode_rawParent edge.parent_eq

theorem storedEdge_degree (edge : RealStoredEdge (Frame.ofMountain before)) :
    (preserved.storedEdge edge).degree = edge.degree := by
  simp only [RealStoredEdge.degree, storedEdge, preserved.mapNode_height]

theorem storedEdge_keyTemplate (hBefore : (Frame.ofMountain before).Ordered)
    (hAfter : (Frame.ofMountain after).Ordered)
    (edge : RealStoredEdge (Frame.ofMountain before)) (D : Nat) :
    (preserved.storedEdge edge).keyTemplate hAfter D =
      Keys.relabel (edge.keyTemplate hBefore D) preserved.keyColumn := by
  funext i
  simp only [RealStoredEdge.keyTemplate, preserved.storedEdge_degree, Keys.relabel]
  split
  · simp only [storedEdge, preserved.mapNode_scaleRoot hBefore hAfter]
    apply congrArg some
    apply Fin.ext
    exact preserved.mapNode_column _
  · rfl

theorem storedEdge_key_eval {Label : Type u} [LinearOrder Label]
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    (edge : RealStoredEdge (Frame.ofMountain before)) (D : Nat)
    (labels : Fin after.size → Label) :
    Keys.eval ((preserved.storedEdge edge).keyTemplate hAfter D) labels =
      Keys.eval (edge.keyTemplate hBefore D) (labels ∘ preserved.keyColumn) := by
  rw [preserved.storedEdge_keyTemplate hBefore hAfter]
  exact Keys.eval_relabel_of_labels _ preserved.keyColumn _ _ (fun _ => rfl)

end PreservesColumns
end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.mapNode_scaleRoot
#print axioms OmegaY.Expansion.PreservesColumns.storedEdge_degree
#print axioms OmegaY.Expansion.PreservesColumns.storedEdge_keyTemplate
#print axioms OmegaY.Expansion.PreservesColumns.storedEdge_key_eval
