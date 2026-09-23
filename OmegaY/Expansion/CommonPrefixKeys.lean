/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonPrefixKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PreservedMountainKeys

/-! Exact keys for edges whose actual parent is in a common complete
prefix and whose lower rows agree. Neither graph need be canonical. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame
universe u

theorem storedEdge_key_eval_of_common_parent
    {common left right : Mountain}
    (leftPreserved : PreservesColumns common left)
    (rightPreserved : PreservesColumns common right)
    (hCommon : (Frame.ofMountain common).Ordered)
    (hLeft : (Frame.ofMountain left).Ordered)
    (hRight : (Frame.ofMountain right).Ordered)
    (leftEdge : RealStoredEdge (Frame.ofMountain left))
    (rightEdge : RealStoredEdge (Frame.ofMountain right))
    (parent : (Frame.ofMountain common).Node)
    (hLeftParent : leftEdge.parent = leftPreserved.mapNode parent)
    (hRightParent : rightEdge.parent = rightPreserved.mapNode parent)
    (hRow : (Frame.ofMountain right).height rightEdge.lower =
      (Frame.ofMountain left).height leftEdge.lower)
    (D : Nat) {Label : Type u} [LinearOrder Label] (labels : Nat → Label) :
    rightEdge.degree = leftEdge.degree ∧
      Keys.eval (rightEdge.keyTemplate hRight D) (fun column => labels column.val) =
        Keys.eval (leftEdge.keyTemplate hLeft D) (fun column => labels column.val) := by
  have hDegree : rightEdge.degree = leftEdge.degree := by
    simp only [RealStoredEdge.degree, hLeftParent, hRightParent,
      leftPreserved.mapNode_height, rightPreserved.mapNode_height, hRow]
  refine ⟨hDegree, ?_⟩
  funext i
  simp only [Keys.eval, Pi.toLex_apply, RealStoredEdge.keyTemplate, hDegree]
  by_cases hActive : leftEdge.degree ≤ D - i.val
  · simp only [if_pos hActive, hLeftParent, hRightParent,
      leftPreserved.mapNode_scaleRoot hCommon hLeft,
      rightPreserved.mapNode_scaleRoot hCommon hRight,
      leftPreserved.mapNode_column, rightPreserved.mapNode_column]
  · simp only [if_neg hActive]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.storedEdge_key_eval_of_common_parent
