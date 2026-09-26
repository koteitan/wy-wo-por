/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialControlKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.TopEdgeKeys
import OmegaY.Geometry.RepresentedMountain
import OmegaY.Expansion.RootGeometry

/-! The actual deleted top edge controls every earlier edge in the old
last column. A single reflection compresses the complete prefix and all
of those actual virtual demands below the actual bad-root label. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem Preparation.initial_pop_size {front : List Nat} {last : Nat}
    (p : Preparation front last) : p.initial.pop.size = front.length := by
  have h := build_size p.initial_build
  simp only [List.length_append, List.length_singleton] at h
  simp only [Array.size_pop, h, Nat.add_sub_cancel]

namespace RootGeometry

variable {front : List Nat} {last : Nat} {p : Preparation front last}

def controlEdge (g : RootGeometry p) : RealStoredEdge (Frame.ofMountain p.initial) where
  lower := g.lower
  upper := g.topNode
  parent := g.rootNode
  lower_real := g.lower_real
  upper_eq := g.lower_upper
  parent_eq := ((build_normal_of_success p.initial_build).rawParent_eq_P g.lower_real).trans
    g.lower_parent

def LowerEdge (g : RootGeometry p) :=
  {edge : RealStoredEdge (Frame.ofMountain p.initial) //
    edge.lower.1.val = front.length ∧ edge.lower.2.val < g.lower.2.val}

def controlAtom (g : RootGeometry p) (D : Nat) : Model.TopAtom (D + 1) p.initial.pop.size :=
  g.controlEdge.topAtom p.initial_valid.toOrdered D p.initial.pop.size
    (g.lower_column.trans p.initial_pop_size.symm)

def lowerAtom (g : RootGeometry p) (D : Nat) (edge : g.LowerEdge) :
    Model.TopAtom (D + 1) p.initial.pop.size :=
  edge.val.topAtom p.initial_valid.toOrdered D p.initial.pop.size
    (edge.property.1.trans p.initial_pop_size.symm)

theorem lower_key_strict (g : RootGeometry p) {D : Nat}
    (hSupported : ∀ w : (Frame.ofMountain p.initial).Node, ∀ i,
      D < i → Row.coeff ((Frame.ofMountain p.initial).height w) i = 0)
    (edge : g.LowerEdge) :
    Keys.templateKey (g.lowerAtom D edge).key < Keys.templateKey (g.controlAtom D).key := by
  exact edge.val.topAtom_key_strict_in_column (build_normal_of_success p.initial_build)
    hSupported g.controlEdge (edge.property.1.trans p.initial_pop_size.symm)
    (g.lower_column.trans p.initial_pop_size.symm) edge.property.2

/-- This consumes an arbitrary representation of the actual original
mountain. It constructs the compressed prefix and simultaneous lower-edge
reservoirs; neither the strict key inequalities nor reservoir relations are
hypotheses. It does not yet assert a representation of a copied block. -/
theorem reflect_initial_control (g : RootGeometry p) {D : Nat}
    (hSupported : ∀ w : (Frame.ofMountain p.initial).Node, ∀ i,
      D < i → Row.coeff ((Frame.ofMountain p.initial).height w) i = 0)
    (representation : KeyRepresentation p.initial_valid.toOrdered D) :
    ∃ fresh : KeyRepresentation p.initial_valid.pop.toOrdered D,
      (∀ column, fresh.labels column < representation.labels g.rootNode.1) ∧
      (∀ column, column.val < p.root.column →
        fresh.labels column = representation.labels
          ((PreservesColumns.pop_prefix p.initial).keyColumn column)) ∧
      (∀ column, fresh.labels column ≤ representation.labels
          ((PreservesColumns.pop_prefix p.initial).keyColumn column)) ∧
      (∀ edge : g.LowerEdge,
        Model.R (D + 1) (Keys.eval (g.lowerAtom D edge).key fresh.labels)
          (fresh.labels (g.lowerAtom D edge).parent) (representation.labels g.rootNode.1)) := by
  classical
  letI : Fintype g.LowerEdge := by unfold LowerEdge; infer_instance
  let preserved := PreservesColumns.pop_prefix p.initial
  let old := representation.restrict preserved p.initial_valid.pop.toOrdered
  let f := old.labels
  let top := representation.labels g.lower.1
  let cut := (g.controlAtom D).parent
  let prefixEdges := (Finset.univ : Finset (RealStoredEdge (Frame.ofMountain p.initial.pop))).toList
  let lowerEdges := (Finset.univ : Finset g.LowerEdge).toList
  let graph := prefixEdges.map (fun edge => edge.atom p.initial_valid.pop.toOrdered D)
  let needs := lowerEdges.map (g.lowerAtom D)
  have hMono : StrictMono f := old.strictMono
  have hBound : Reflection.Bounded f top := by
    intro column
    apply representation.strictMono
    change column.val < g.lower.1.val
    rw [g.lower_column, ← p.initial_pop_size]
    exact column.isLt
  have hGraph : Reflection.InternalHolds (Model.keySyntax (D + 1)) (Model.R (D + 1)) graph f := by
    intro atom hAtom
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hAtom
    exact old.edges edge
  have hKeys : Reflection.KeysBelow (Model.keySyntax (D + 1)) needs f
      (Keys.eval (g.controlAtom D).key f) := by
    intro atom hAtom
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hAtom
    exact Keys.eval_lt_of_template_lt _ _ f hMono (g.lower_key_strict hSupported edge)
  have hNeeds : Reflection.TopHolds (Model.keySyntax (D + 1)) (Model.R (D + 1)) needs f top := by
    intro atom hAtom
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hAtom
    have hEval := edge.val.topAtom_key_eval p.initial_valid.toOrdered D p.initial.pop.size
      (edge.property.1.trans p.initial_pop_size.symm) preserved.size_le representation.labels
    change Keys.eval (g.lowerAtom D edge).key f = _ at hEval
    change Model.R (D + 1) (Keys.eval (g.lowerAtom D edge).key f) _ _
    rw [hEval]
    have hChild : edge.val.lower.1 = g.lower.1 :=
      Fin.ext (edge.property.1.trans g.lower_column.symm)
    have h := representation.edges edge.val
    rw [hChild] at h
    exact h
  have hControl : Model.R (D + 1) (Keys.eval (g.controlAtom D).key f) (f cut) top := by
    have hEval := g.controlEdge.topAtom_key_eval p.initial_valid.toOrdered D p.initial.pop.size
      (g.lower_column.trans p.initial_pop_size.symm) preserved.size_le representation.labels
    change Keys.eval (g.controlAtom D).key f = _ at hEval
    rw [hEval]
    exact representation.edges g.controlEdge
  obtain ⟨labels, hLabels, hBelow, hFixed, hLe, hNewGraph, hNewNeeds⟩ :=
    Model.finite_reflection graph needs f cut hMono hBound hGraph hKeys hNeeds hControl
  have hCut : f cut = representation.labels g.rootNode.1 := rfl
  let fresh : KeyRepresentation p.initial_valid.pop.toOrdered D := {
    labels := labels
    strictMono := hLabels
    bounded := fun column => (hBelow column).trans (by rw [hCut]; exact representation.bounded _)
    edges := fun edge => hNewGraph (edge.atom p.initial_valid.pop.toOrdered D)
      (List.mem_map.mpr ⟨edge, by simp [prefixEdges], rfl⟩) }
  refine ⟨fresh, ?_, ?_, hLe, ?_⟩
  · intro column
    exact (hBelow column).trans_eq hCut
  · intro column hColumn
    apply hFixed
    have hRoot : g.rootNode.1.val = p.root.column := congrArg Ref.column g.root_ref
    change column.val < g.rootNode.1.val
    omega
  · intro edge
    have h := hNewNeeds (g.lowerAtom D edge)
      (List.mem_map.mpr ⟨edge, by simp [lowerEdges], rfl⟩)
    rw [hCut] at h
    exact h

end RootGeometry
end OmegaY.Expansion

#print axioms OmegaY.Expansion.RootGeometry.lower_key_strict
#print axioms OmegaY.Expansion.RootGeometry.reflect_initial_control
