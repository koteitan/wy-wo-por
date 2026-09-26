/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/VerticalEdgeKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.VerticalRoots

/-!
# Strict ordering of the actual stored-edge keys in a normal column

This is a consequence of the strong vertical root theorem, not of a
single root coordinate or of a numerical bound. Infinity suffixes are
the literal suffixes of the reflection model's key domain.
-/

namespace OmegaY.Geometry.Frame

universe u

private theorem truncate_full_le {Label : Type u} [LinearOrder Label] {m : Nat}
    (roots : Fin m → Label) (keep : Nat) :
    Keys.truncate roots m ≤ Keys.truncate roots keep := by
  apply Pi.toLex_monotone
  intro i
  simp only [if_pos i.isLt]
  split_ifs
  · exact le_rfl
  · exact le_top

/-- A strict difference within the left key's finite prefix decides the
comparison even if the right key is truncated at a different scale. -/
theorem rootPrefix_lt_arbitrary_truncate {F : Frame} (hF : F.Ordered) {D k : Nat}
    {u v : F.Node} {Label : Type u} [LinearOrder Label]
    (f : Fin F.width → Label) (hf : StrictMono f)
    (h : rootPrefix hF D k u < rootPrefix hF D k v) (keepRight : Nat) :
    Keys.truncate (fun i : Fin (D + 1) => f (scaleRoot hF (D - i.val) u).1)
        (D + 1 - k) <
      Keys.truncate (fun i : Fin (D + 1) => f (scaleRoot hF (D - i.val) v).1)
        keepRight := by
  obtain ⟨i, hki, hiD, hHigher, hAt⟩ := rootPrefix_lt_witness hF h
  let index : Fin (D + 1) := ⟨D - i, by omega⟩
  have hIndex : index.val < D + 1 - k := by dsimp only [index]; omega
  apply lt_of_lt_of_le (b := Keys.truncate
    (fun j : Fin (D + 1) => f (scaleRoot hF (D - j.val) v).1) (D + 1))
  · apply Keys.truncate_lt_at index hIndex index.isLt
    · intro j hj
      apply congrArg f
      apply hHigher (D - j.val)
      · have hj' : j.val < D - i := hj
        omega
      · omega
    · have he : D - index.val = i := by dsimp only [index]; omega
      simpa only [he] using hf hAt
  · exact truncate_full_le _ keepRight

namespace RealStoredEdge

theorem eval_keyTemplate_eq_lower_truncate {F : Frame} (e : RealStoredEdge F)
    {Label : Type u} [LinearOrder Label] (hF : F.Ordered) {D : Nat}
    (hDegree : e.degree ≤ D) (f : Fin F.width → Label) :
    Keys.eval (e.keyTemplate hF D) f =
      Keys.truncate (fun i : Fin (D + 1) => f (scaleRoot hF (D - i.val) e.lower).1)
        (D + 1 - e.degree) := by
  rw [e.eval_keyTemplate_eq_truncate hF hDegree f]
  apply funext
  intro i
  simp only [Keys.truncate, Pi.toLex_apply]
  by_cases hi : i.val < D + 1 - e.degree
  · have hScale : e.degree ≤ D - i.val := by have := i.isLt; omega
    simp only [if_pos hi, scaleRoot_eq_of_raw hF e.parent_eq hScale]
  · simp only [if_neg hi]

private theorem same_column_height_le {F : Frame} (hF : F.Ordered) {a b : F.Node}
    (hc : a.1 = b.1) (hi : a.2.val ≤ b.2.val) : F.height a ≤ F.height b := by
  rcases a with ⟨c, i⟩
  rcases b with ⟨d, j⟩
  dsimp only at hc hi
  subst d
  exact (hF.rows_strict c).monotone hi

/-- Every actual lower stored edge has strictly smaller key than every
higher stored edge of the same normal column. Arbitrary increasing labels
are allowed; no ordinal reflection model is assumed here. -/
theorem key_strict_in_column {F : Frame} (hF : F.Normal) {D : Nat}
    (hSupported : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0)
    (e f : RealStoredEdge F) (hColumn : e.lower.1 = f.lower.1)
    (hIndex : e.lower.2.val < f.lower.2.val)
    {Label : Type u} [LinearOrder Label] (labels : Fin F.width → Label)
    (hLabels : StrictMono labels) :
    Keys.eval (e.keyTemplate hF.toOrdered D) labels <
      Keys.eval (f.keyTemplate hF.toOrdered D) labels := by
  have hEUpper := upper_spec e.upper_eq
  have hUpperIndex : e.upper.2.val ≤ f.lower.2.val := by omega
  have hLowerUpper : F.height e.lower ≤ F.height e.upper :=
    same_column_height_le hF.toOrdered hEUpper.1.symm (by omega)
  have hUpperLower : F.height e.upper ≤ F.height f.lower :=
    same_column_height_le hF.toOrdered (hEUpper.1.trans hColumn) hUpperIndex
  have hBetween := Row.jump_le_between hLowerUpper hUpperLower
    (Nat.le_refl (Row.jump (F.height e.lower) (F.height f.lower)))
  have hJump := e.degree_from_vertical_jump hF.rawRowGeometry
  have hScale : e.degree < Row.jump (F.height e.lower) (F.height f.lower) := by omega
  have hVertical := hF.rootVertical hSupported e.lower_real hColumn hIndex e.degree hScale
  rw [e.eval_keyTemplate_eq_lower_truncate hF.toOrdered
      (e.degree_le hF.rawRowGeometry (hSupported e.upper)),
    f.eval_keyTemplate_eq_lower_truncate hF.toOrdered
      (f.degree_le hF.rawRowGeometry (hSupported f.upper))]
  exact rootPrefix_lt_arbitrary_truncate hF.toOrdered labels hLabels hVertical _

/-- The purely combinatorial template order is itself strict, before any
ordinal label assignment is chosen. -/
theorem templateKey_strict_in_column {F : Frame} (hF : F.Normal) {D : Nat}
    (hSupported : ∀ w : F.Node, ∀ i, D < i → Row.coeff (F.height w) i = 0)
    (e f : RealStoredEdge F) (hColumn : e.lower.1 = f.lower.1)
    (hIndex : e.lower.2.val < f.lower.2.val) :
    Keys.templateKey (e.keyTemplate hF.toOrdered D) <
      Keys.templateKey (f.keyTemplate hF.toOrdered D) :=
  key_strict_in_column hF hSupported e f hColumn hIndex id (fun _ _ h => h)

end RealStoredEdge

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.RealStoredEdge.key_strict_in_column
#print axioms OmegaY.Geometry.Frame.RealStoredEdge.templateKey_strict_in_column
