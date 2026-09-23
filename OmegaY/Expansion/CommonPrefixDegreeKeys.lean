/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonPrefixDegreeKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CommonPrefixKeys

/-! A key depends on its edge degree and actual parent scale roots, not
separately on its lower row. This form also applies to real graft seams. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame
universe u

theorem storedEdge_key_eval_of_common_parent_degree
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
    (hDegree : rightEdge.degree = leftEdge.degree)
    (D : Nat) {Label : Type u} [LinearOrder Label] (labels : Nat → Label) :
    Keys.eval (rightEdge.keyTemplate hRight D) (fun column => labels column.val) =
      Keys.eval (leftEdge.keyTemplate hLeft D) (fun column => labels column.val) := by
  funext i
  simp only [Keys.eval, Pi.toLex_apply, RealStoredEdge.keyTemplate, hDegree]
  by_cases hActive : leftEdge.degree ≤ D - i.val
  · simp only [if_pos hActive, hLeftParent, hRightParent,
      leftPreserved.mapNode_scaleRoot hCommon hLeft,
      rightPreserved.mapNode_scaleRoot hCommon hRight,
      leftPreserved.mapNode_column, rightPreserved.mapNode_column]
  · simp only [if_neg hActive]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.storedEdge_key_eval_of_common_parent_degree
