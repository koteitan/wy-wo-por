/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FiniteRawSearchInduction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawSearchInduction

/-!
# Finite strict-left / strictly-higher induction

The induction order is on the finite stored nodes of one result mountain:
column number first, then the number of indices above the current node.
It is independent of any well-foundedness assertion about expansions.
The final theorem still requires the local numerical-recognition step.
-/

namespace OmegaY.Geometry.Frame

theorem Ordered.reverse_index_lt_of_higher {F : Frame} (hF : F.Ordered)
    {u v : F.Node} (hColumn : v.1 = u.1) (hHeight : F.height u < F.height v) :
    F.length v.1 - v.2.val < F.length u.1 - u.2.val := by
  cases u with
  | mk c i =>
    cases v with
    | mk d j =>
      dsimp only at hColumn
      subst d
      have hIndex : i < j := (hF.rows_strict c).lt_iff_lt.mp hHeight
      have hBound := j.isLt
      change i.val < j.val at hIndex
      dsimp only
      omega

/-- An ordinary finite-node induction, with no expansion relation involved. -/
theorem Ordered.left_higher_induction {F : Frame} (hF : F.Ordered)
    {motive : F.Node → Prop}
    (step : ∀ u,
      (∀ v, v.1.val < u.1.val → motive v) →
      (∀ v, v.1 = u.1 → F.height u < F.height v → motive v) → motive u)
    (u : F.Node) : motive u := by
  generalize hc : u.1.val = c
  induction c using Nat.strongRecOn generalizing u with
  | ind c outer =>
    generalize hi : F.length u.1 - u.2.val = i
    induction i using Nat.strongRecOn generalizing u with
    | ind i inner =>
      apply step u
      · intro v hLeft
        exact outer v.1.val (by omega) v rfl
      · intro v hColumn hHeight
        have hRank := hF.reverse_index_lt_of_higher hColumn hHeight
        exact inner (F.length v.1 - v.2.val) (by omega) v
          (by simpa only [hColumn] using hc) rfl

/-- Assemble local recognition steps. Left and higher hypotheses are
discharged by finite induction rather than being global premises. -/
theorem rawParentSearch_of_strict_left_higher {F : Frame} (hF : F.Ordered)
    (step : ∀ (u parent : F.Node), Real u → F.rawParent u = some parent →
      (∀ v q, v.1.val < u.1.val → Real v →
        F.rawParent v = some q → F.P v = some q) →
      (∀ v q, v.1 = u.1 → F.height u < F.height v → Real v →
        F.rawParent v = some q → F.P v = some q) → F.P u = some parent) :
    F.RawParentSearch := by
  have hAll : ∀ u, Real u → ∀ parent, F.rawParent u = some parent →
      F.P u = some parent := by
    intro current
    refine hF.left_higher_induction
      (motive := fun u => Real u → ∀ parent,
        F.rawParent u = some parent → F.P u = some parent) ?_ current
    intro u hLeft hHigher hReal parent hRaw
    exact step u parent hReal hRaw
      (fun v q hColumn hv hq => hLeft v hColumn hv q hq)
      (fun v q hColumn hHeight hv hq => hHigher v hColumn hHeight hv q hq)
  intro u parent hReal hRaw
  exact hAll u hReal parent hRaw

end OmegaY.Geometry.Frame

#print axioms OmegaY.Geometry.Frame.Ordered.reverse_index_lt_of_higher
#print axioms OmegaY.Geometry.Frame.Ordered.left_higher_induction
#print axioms OmegaY.Geometry.Frame.rawParentSearch_of_strict_left_higher
