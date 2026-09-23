/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DecrementKeyClassification.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.DecrementLowerKeys
import OmegaY.Expansion.DecrementSeamKeys
import OmegaY.Expansion.PreservedEdgePreimage

/-! Exhaustive inverse provenance for the keys of actual decrement edges.
Retained prefix edges, old last-column lower edges, and genuine old root
edges are kept separate because they use different reflected relations. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

inductive DecrementKeyOrigin {front : List Nat} {last : Nat}
    (p : Preparation front last) (g : RootGeometry p)
    (edge : RealStoredEdge (Frame.ofMountain p.reduced)) : Prop
  | retained (oldEdge : RealStoredEdge (Frame.ofMountain p.initial.pop))
      (hEdge : p.initial_pop_preserved_reduced.storedEdge oldEdge = edge)
  | lower (oldEdge : g.LowerEdge)
      (hColumn : edge.lower.1.val = front.length)
      (hParent : Frame.ref oldEdge.val.parent = Frame.ref edge.parent)
      (hDegree : edge.degree = oldEdge.val.degree)
      (hKey : ∀ (D : Nat) (labels : Nat → Model.Label),
        Keys.eval (edge.keyTemplate p.reduced_valid.toOrdered D) (fun c => labels c.val) =
          Keys.eval (oldEdge.val.keyTemplate p.initial_valid.toOrdered D) (fun c => labels c.val))
  | grafted (oldEdge : RealStoredEdge (Frame.ofMountain p.initial))
      (hColumn : edge.lower.1.val = front.length)
      (hOldColumn : oldEdge.lower.1.val = p.root.column)
      (hParent : Frame.ref oldEdge.parent = Frame.ref edge.parent)
      (hDegree : edge.degree = oldEdge.degree)
      (hKey : ∀ (D : Nat) (labels : Nat → Model.Label),
        Keys.eval (edge.keyTemplate p.reduced_valid.toOrdered D) (fun c => labels c.val) =
          Keys.eval (oldEdge.keyTemplate p.initial_valid.toOrdered D) (fun c => labels c.val))

theorem Preparation.reduced_edge_key_origin
    {front : List Nat} {last : Nat} (p : Preparation front last)
    (g : RootGeometry p) (hLast : 1 < last)
    (edge : RealStoredEdge (Frame.ofMountain p.reduced)) :
    DecrementKeyOrigin p g edge := by
  by_cases hBefore : edge.lower.1.val < p.initial.pop.size
  · obtain ⟨oldEdge, hEdge⟩ := p.initial_pop_preserved_reduced.storedEdge_preimage
      p.reduced_valid.toOrdered edge hBefore
    exact .retained oldEdge hEdge
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hBound : edge.lower.1.val < p.reduced.size := edge.lower.1.isLt
  have hColumn : edge.lower.1.val = front.length := by rw [p.initial_pop_size] at hBefore; omega
  by_cases hUpperLow : (Frame.ofMountain p.reduced).height edge.upper < p.lastTop.row
  · obtain ⟨oldEdge, hParent, hDegree, hKey⟩ :=
      p.reduced_lower_edge_key g hLast edge hColumn hUpperLow
    exact .lower oldEdge hColumn hParent hDegree hKey
  have hUpperHigh := le_of_not_gt hUpperLow
  by_cases hLowerLow : (Frame.ofMountain p.reduced).height edge.lower < p.lastTop.row
  · obtain ⟨oldEdge, hRoot, _, hParent, hDegree, hKey⟩ :=
      p.reduced_seam_edge_key hLast edge hColumn hLowerLow hUpperHigh
    exact .grafted oldEdge hColumn (congrArg Ref.column hRoot) hParent.symm hDegree hKey
  · obtain ⟨oldEdge, hRootColumn, _, _, _, hParent, hDegree, hKey⟩ :=
      p.reduced_high_edge_key hLast edge hColumn (le_of_not_gt hLowerLow)
    exact .grafted oldEdge hColumn hRootColumn hParent hDegree hKey

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.reduced_edge_key_origin
