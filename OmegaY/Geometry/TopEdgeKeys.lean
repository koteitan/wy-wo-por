/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/TopEdgeKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.VerticalEdgeKeys
import OmegaY.Keys.Prefix

/-! Actual last-column edges as virtual-top demands. Every parameter is
strictly before the child column, so the restriction loses no finite root
and retains the literal infinity suffix. -/

namespace OmegaY.Geometry.Frame.RealStoredEdge

universe u
variable {F : Frame}

def topAtom (edge : RealStoredEdge F) (hF : F.Ordered) (D n : Nat)
    (hColumn : edge.lower.1.val = n) : Model.TopAtom (D + 1) n where
  key := Keys.restrictPrefix (edge.keyTemplate hF D) n (by
    intro i column h
    exact (edge.keyTemplate_column_bound hF h).2.trans_eq hColumn)
  parent := ⟨edge.parent.1.val, (rawParent_column_lt hF edge.parent_eq).trans_eq hColumn⟩

theorem topAtom_key_eval (edge : RealStoredEdge F) (hF : F.Ordered) (D n : Nat)
    (hColumn : edge.lower.1.val = n) (hWidth : n ≤ F.width)
    {Label : Type u} [LinearOrder Label] (labels : Fin F.width → Label) :
    Keys.eval (edge.topAtom hF D n hColumn).key (labels ∘ Fin.castLE hWidth) =
      Keys.eval (edge.keyTemplate hF D) labels := by
  have h := Keys.eval_relabel_of_labels (edge.topAtom hF D n hColumn).key
    (Fin.castLE hWidth) (labels ∘ Fin.castLE hWidth) labels (fun _ => rfl)
  change Keys.eval (Keys.relabel (Keys.restrictPrefix _ n _) (Fin.castLE hWidth)) labels = _ at h
  rw [Keys.relabel_restrictPrefix] at h
  exact h.symm

theorem topAtom_key_strict_in_column (hF : F.Normal) {D n : Nat}
    (hSupported : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0)
    (edge control : RealStoredEdge F)
    (hEdgeColumn : edge.lower.1.val = n) (hControlColumn : control.lower.1.val = n)
    (hIndex : edge.lower.2.val < control.lower.2.val) :
    Keys.templateKey (edge.topAtom hF.toOrdered D n hEdgeColumn).key <
      Keys.templateKey (control.topAtom hF.toOrdered D n hControlColumn).key := by
  apply (Keys.restrictPrefix_lt_iff _ _ _ _ (by
    have := control.lower.1.isLt
    omega)).mpr
  exact edge.templateKey_strict_in_column hF hSupported control
    (Fin.ext (hEdgeColumn.trans hControlColumn.symm)) hIndex

end OmegaY.Geometry.Frame.RealStoredEdge

#print axioms OmegaY.Geometry.Frame.RealStoredEdge.topAtom_key_eval
#print axioms OmegaY.Geometry.Frame.RealStoredEdge.topAtom_key_strict_in_column
