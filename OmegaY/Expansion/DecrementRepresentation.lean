/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DecrementRepresentation.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.DecrementKeyClassification

/-! A genuine ordinal representation of the executed decrement mountain.
Finite reflection supplies the complete compressed prefix and all retained
lower-edge demands. The new last label is the old root label. Grafted root
edges use the old representation, since all their finite parameters and
their parent lie strictly in the unchanged good part. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

private theorem eval_eq_on_support {m n : Nat} (key : Keys.Template m n)
    (left right : Fin n → Model.Label)
    (hLabels : ∀ i column, key i = some column → left column = right column) :
    Keys.eval key left = Keys.eval key right := by
  funext i
  simp only [Keys.eval, Pi.toLex_apply]
  cases h : key i with
  | none => rfl
  | some column => exact congrArg (fun x : Model.Label => (x : WithTop Model.Label)) (hLabels i column h)

namespace RootGeometry

variable {front : List Nat} {last : Nat} {p : Preparation front last}

/-- Reflection of the actual control edge is sufficient to represent the
whole reduced mountain, including the first graft seam. -/
theorem represent_decrement (g : RootGeometry p) (hLast : 1 < last) {D : Nat}
    (hSupported : ∀ w : (Frame.ofMountain p.initial).Node, ∀ i,
      D < i → Row.coeff ((Frame.ofMountain p.initial).height w) i = 0)
    (representation : KeyRepresentation p.initial_valid.toOrdered D) :
    ∃ fresh : KeyRepresentation p.reduced_valid.toOrdered D,
      (∀ column, fresh.labels column ≤ representation.labels g.rootNode.1) ∧
      (∀ column, column.val < front.length →
        fresh.labels column < representation.labels g.rootNode.1) ∧
      (∀ column, column.val = front.length →
        fresh.labels column = representation.labels g.rootNode.1) ∧
      (∀ column (hGood : column.val < p.root.column),
        fresh.labels column = representation.labels
          ⟨column.val, by
            exact lt_trans hGood ((congrArg Ref.column g.root_ref).symm.trans_lt
              g.rootNode.1.isLt)⟩) := by
  obtain ⟨compressed, hBelow, hFixed, _hLe, hNeeds⟩ :=
    g.reflect_initial_control hSupported representation
  let oldPreserved := PreservesColumns.pop_prefix p.initial
  let newPreserved := p.initial_pop_preserved_reduced
  let n := p.initial.pop.size
  let apex := representation.labels g.rootNode.1
  let labels : Nat → Model.Label := fun column =>
    if hColumn : column < n then compressed.labels ⟨column, hColumn⟩ else apex
  have hn : n = front.length := p.initial_pop_size
  have hNewSize : p.reduced.size = n + 1 := by
    have h := build_size p.reduced_build
    simpa only [List.length_append, List.length_singleton, hn] using h
  have hRootColumn : g.rootNode.1.val = p.root.column := congrArg Ref.column g.root_ref
  have hRootBefore : p.root.column < n := by
    have h := P_column_lt (build_normal_of_success p.initial_build).toOrdered g.lower_parent
    rw [g.lower_column, hRootColumn, ← hn] at h
    exact h
  have hLabelsBefore (column : Fin n) : labels column.val = compressed.labels column := by
    simp only [labels, column.isLt, ↓reduceDIte]
    exact congrArg compressed.labels (Fin.ext rfl)
  have hLabelsLast : labels n = apex := by simp only [labels, lt_self_iff_false, ↓reduceDIte]
  have hLabelsGood (column : Fin p.initial.size) (hGood : column.val < p.root.column) :
      labels column.val = representation.labels column := by
    have hBefore : column.val < n := hGood.trans hRootBefore
    rw [show labels column.val = compressed.labels ⟨column.val, hBefore⟩ by
      simp only [labels, hBefore, ↓reduceDIte]]
    exact hFixed ⟨column.val, hBefore⟩ hGood
  have hAllBelow (column : Fin p.reduced.size) : labels column.val ≤ apex := by
    by_cases hBefore : column.val < n
    · exact (hLabelsBefore ⟨column.val, hBefore⟩).trans_le (hBelow _).le
    · have hColumn : column.val = n := by have := column.isLt; omega
      exact (congrArg labels hColumn).trans hLabelsLast |>.le
  have hMono : StrictMono (fun column : Fin p.reduced.size => labels column.val) := by
    intro left right hlt
    change labels left.val < labels right.val
    have hRight : right.val < n + 1 := by simpa only [hNewSize] using right.isLt
    have hLeft : left.val < n := by change left.val < right.val at hlt; omega
    by_cases hBefore : right.val < n
    · exact (hLabelsBefore ⟨left.val, hLeft⟩).trans_lt
        ((compressed.strictMono hlt).trans_eq (hLabelsBefore ⟨right.val, hBefore⟩).symm)
    · have he : right.val = n := by omega
      exact (hLabelsBefore ⟨left.val, hLeft⟩).trans_lt
        ((hBelow _).trans_eq ((congrArg labels he).trans hLabelsLast).symm)
  have hEdges (edge : RealStoredEdge (Frame.ofMountain p.reduced)) :
      Model.R (D + 1) (Keys.eval (edge.keyTemplate p.reduced_valid.toOrdered D)
        (fun column => labels column.val)) (labels edge.parent.1.val) (labels edge.lower.1.val) := by
    cases p.reduced_edge_key_origin g hLast edge with
    | retained oldEdge hEdge =>
      subst edge
      have hKey := newPreserved.storedEdge_key_eval
        p.initial_valid.pop.toOrdered p.reduced_valid.toOrdered oldEdge D
        (fun column => labels column.val)
      change Keys.eval ((p.initial_pop_preserved_reduced.storedEdge oldEdge).keyTemplate
        p.reduced_valid.toOrdered D) (fun c => labels c.val) =
        Keys.eval (oldEdge.keyTemplate p.initial_valid.pop.toOrdered D)
          (fun c => labels c.val) at hKey
      rw [hKey]
      have hRestrict : (fun column : Fin n => labels column.val) =
          compressed.labels := funext hLabelsBefore
      have hEval := congrArg (Keys.eval (oldEdge.keyTemplate p.initial_valid.pop.toOrdered D)) hRestrict
      have hRelationKey := congrArg (fun key => Model.R (D + 1) key
        (labels oldEdge.parent.1.val) (labels oldEdge.lower.1.val)) hEval
      have hRelationLabels := congrArg₂
        (Model.R (D + 1) (Keys.eval (oldEdge.keyTemplate p.initial_valid.pop.toOrdered D) compressed.labels))
        (hLabelsBefore oldEdge.parent.1) (hLabelsBefore oldEdge.lower.1)
      have hParentColumn : (p.initial_pop_preserved_reduced.storedEdge oldEdge).parent.1.val =
          oldEdge.parent.1.val := p.initial_pop_preserved_reduced.mapNode_column oldEdge.parent
      have hChildColumn : (p.initial_pop_preserved_reduced.storedEdge oldEdge).lower.1.val =
          oldEdge.lower.1.val := p.initial_pop_preserved_reduced.mapNode_column oldEdge.lower
      rw [hParentColumn, hChildColumn]
      exact (hRelationKey.trans hRelationLabels).mpr (compressed.edges oldEdge)
    | lower oldEdge hColumn hParent _hDegree hKey =>
      rw [hKey D labels]
      have hEval := oldEdge.val.topAtom_key_eval p.initial_valid.toOrdered D n
        (oldEdge.property.1.trans hn.symm) oldPreserved.size_le
        (fun column => labels column.val)
      change Keys.eval (g.lowerAtom D oldEdge).key (fun c => labels c.val) =
        Keys.eval (oldEdge.val.keyTemplate p.initial_valid.toOrdered D)
          (fun c => labels c.val) at hEval
      have hRestrict : (fun column : Fin n => labels column.val) =
          compressed.labels := funext hLabelsBefore
      rw [hRestrict] at hEval
      change Keys.eval (g.lowerAtom D oldEdge).key compressed.labels = _ at hEval
      rw [← hEval]
      have hParentColumn : oldEdge.val.parent.1.val = edge.parent.1.val := congrArg Ref.column hParent
      have hParentLabel : labels edge.parent.1.val = compressed.labels (g.lowerAtom D oldEdge).parent := by
        rw [← hParentColumn]
        exact hLabelsBefore (g.lowerAtom D oldEdge).parent
      rw [hParentLabel, hColumn, ← hn, hLabelsLast]
      exact hNeeds oldEdge
    | grafted oldEdge hColumn hOldColumn hParent _hDegree hKey =>
      rw [hKey D labels]
      have hParentGood : oldEdge.parent.1.val < p.root.column :=
        (rawParent_column_lt p.initial_valid.toOrdered oldEdge.parent_eq).trans_eq hOldColumn
      have hEval : Keys.eval (oldEdge.keyTemplate p.initial_valid.toOrdered D)
          (fun column => labels column.val) =
          Keys.eval (oldEdge.keyTemplate p.initial_valid.toOrdered D) representation.labels := by
        apply eval_eq_on_support
        intro i column hi
        exact hLabelsGood column ((oldEdge.keyTemplate_column_bound p.initial_valid.toOrdered hi).1.trans_lt hParentGood)
      have hParentColumn : oldEdge.parent.1.val = edge.parent.1.val := congrArg Ref.column hParent
      have hChild : oldEdge.lower.1 = g.rootNode.1 := Fin.ext (hOldColumn.trans hRootColumn.symm)
      rw [hEval, ← hParentColumn, hLabelsGood oldEdge.parent.1 hParentGood,
        hColumn, ← hn, hLabelsLast]
      simpa only [hChild] using representation.edges oldEdge
  let fresh : KeyRepresentation p.reduced_valid.toOrdered D := {
    labels := fun column => labels column.val
    strictMono := hMono
    bounded := fun column => (hAllBelow column).trans_lt (representation.bounded g.rootNode.1)
    edges := hEdges }
  refine ⟨fresh, hAllBelow, ?_, ?_, ?_⟩
  · intro column hColumn
    have hBefore : column.val < n := hColumn.trans_eq hn.symm
    exact (hLabelsBefore ⟨column.val, hBefore⟩).trans_lt (hBelow _)
  · intro column hColumn
    exact (congrArg labels (hColumn.trans hn.symm)).trans hLabelsLast
  · intro column hGood
    exact hLabelsGood ⟨column.val, lt_trans hGood (hRootColumn.symm.trans_lt g.rootNode.1.isLt)⟩ hGood

end RootGeometry

/-- The automatically constructed decrement representation lies strictly
below the original last label. This is the complete decrement stage;
the subsequent positive-copy blocks are a separate construction. -/
theorem Preparation.represent_decrement_descent
    {front : List Nat} {last : Nat} (p : Preparation front last)
    (hLast : 1 < last) {D : Nat}
    (hSupported : ∀ w : (Frame.ofMountain p.initial).Node, ∀ i,
      D < i → Row.coeff ((Frame.ofMountain p.initial).height w) i = 0)
    (representation : KeyRepresentation p.initial_valid.toOrdered D) :
    ∃ (hWidth : 0 < p.initial.size)
      (fresh : KeyRepresentation p.reduced_valid.toOrdered D),
      ∀ column, fresh.labels column < representation.lastLabel hWidth := by
  obtain ⟨g⟩ := p.root_geometry hLast
  obtain ⟨fresh, hBound, _, _, _⟩ := g.represent_decrement hLast hSupported representation
  have hSize := build_size p.initial_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hWidth : 0 < p.initial.size := by omega
  have hRootLt : representation.labels g.rootNode.1 < representation.labels g.lower.1 :=
    representation.strictMono (P_column_lt (build_normal_of_success p.initial_build).toOrdered g.lower_parent)
  have hLastLabel : representation.labels g.lower.1 = representation.lastLabel hWidth := by
    apply congrArg representation.labels
    apply Fin.ext
    change g.lower.1.val = p.initial.size - 1
    rw [g.lower_column, hSize]
    omega
  exact ⟨hWidth, fresh, fun column => ((hBound column).trans_lt hRootLt).trans_eq hLastLabel⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.RootGeometry.represent_decrement
#print axioms OmegaY.Expansion.Preparation.represent_decrement_descent
