/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualInitialReservoir.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSpliceFacts

/-!
# The initial actual reservoir from an arbitrary old representation

All labels are the restriction of the given original representation.
Every internal fact, lower virtual fact and the control relation is read
from an actual old edge. No initial-representation existence theorem and
no reflection or decrement representation are used in this base step.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem actual_graph_cast_eq {before after : Mountain} {D n : Nat}
    (h : before = after) (hBefore : (Frame.ofMountain before).Ordered)
    (hAfter : (Frame.ofMountain after).Ordered) (hBeforeSize : before.size = n)
    (hAfterSize : after.size = n) :
    (actualStoredEdges (Frame.ofMountain before)).map (fun edge =>
      Splice.mapAtom (Fin.cast hBeforeSize) (Splice.fin_cast_strictMono _)
        (edge.atom hBefore D)) =
    (actualStoredEdges (Frame.ofMountain after)).map (fun edge =>
      Splice.mapAtom (Fin.cast hAfterSize) (Splice.fin_cast_strictMono _)
        (edge.atom hAfter D)) := by
  subst after
  rfl

namespace Preparation

variable {front : List Nat} {last : Nat} (p : Preparation front last)

noncomputable def initialSpliceLabels {D : Nat}
    (representation : KeyRepresentation p.initial_valid.toOrdered D) : Fin front.length → Model.Label :=
  fun column => (representation.restrict (PreservesColumns.pop_prefix p.initial)
    p.initial_valid.pop.toOrdered).labels (Fin.cast p.initial_pop_size.symm column)

theorem initialSpliceLabels_cast {D : Nat}
    (representation : KeyRepresentation p.initial_valid.toOrdered D)
    (column : Fin (Frame.ofMountain p.initial.pop).width) :
    p.initialSpliceLabels representation (Fin.cast p.initial_pop_size column) =
      (representation.restrict (PreservesColumns.pop_prefix p.initial)
        p.initial_valid.pop.toOrdered).labels column := rfl

theorem initialSpliceLabels_value {D : Nat}
    (representation : KeyRepresentation p.initial_valid.toOrdered D)
    (column : Fin front.length) :
    p.initialSpliceLabels representation column = representation.labels
      ⟨column.val, by
        have hi := column.isLt
        have hs := build_size p.initial_build
        simp only [List.length_append, List.length_singleton] at hs
        change column.val < p.initial.size
        omega⟩ := rfl

theorem spliceGraph_zero (hLast : 1 < last) (D : Nat)
    (hSize : front.length = Splice.blockWidth front.length p.root.column 0) :
    p.spliceGraph hLast D 0 = (p.initialSpliceFacts D).map
      (Splice.mapAtom (Fin.cast hSize) (Splice.fin_cast_strictMono _)) := by
  classical
  have hGraph := actual_graph_cast_eq (D := D) (p.spliceMountain_zero hLast)
    (p.spliceMountain_valid hLast 0).toOrdered p.initial_valid.pop.toOrdered
    (p.spliceMountain_size hLast 0) (p.initial_pop_size.trans hSize)
  change p.spliceGraph hLast D 0 = _ at hGraph
  rw [hGraph]
  unfold initialSpliceFacts initialSpliceEdgeAtom
  refine Eq.trans ?_ List.map_map.symm
  apply List.map_congr_left
  intro edge _
  apply spliceAtom_eq_of_fields
  · change Keys.relabel (edge.keyTemplate p.initial_valid.pop.toOrdered D)
        (Fin.cast (p.initial_pop_size.trans hSize)) =
      Keys.relabel (Keys.relabel (edge.keyTemplate p.initial_valid.pop.toOrdered D)
        (Fin.cast p.initial_pop_size)) (Fin.cast hSize)
    funext i
    simp only [Keys.relabel]
    cases (edge.keyTemplate p.initial_valid.pop.toOrdered D) i <;> rfl
  · exact Fin.ext rfl
  · exact Fin.ext rfl

noncomputable def zeroSpliceLabels {D : Nat}
    (representation : KeyRepresentation p.initial_valid.toOrdered D) :
    Fin (Splice.blockWidth front.length p.root.column 0) → Model.Label :=
  fun column => p.initialSpliceLabels representation
    (Fin.cast (by simp [Splice.blockWidth]) column)

theorem zeroSpliceLabels_source {D : Nat}
    (representation : KeyRepresentation p.initial_valid.toOrdered D) (column : Fin front.length) :
    p.zeroSpliceLabels representation (Splice.blockSource p.root_before_last 0 column) =
      p.initialSpliceLabels representation column := by
  apply congrArg (p.initialSpliceLabels representation)
  apply Fin.ext
  exact Splice.blockSource_zero p.root_before_last column

end Preparation

namespace RootGeometry

variable {front : List Nat} {last : Nat} {p : Preparation front last}

/-- The original last-column label is exactly the external reservoir
bound, irrespective of which row supplies the actual control edge. -/
theorem initialSpliceBeta_eq_lastLabel (g : RootGeometry p) {D : Nat}
    (representation : KeyRepresentation p.initial_valid.toOrdered D) :
    ∃ hWidth : 0 < p.initial.size,
      representation.labels g.lower.1 = representation.lastLabel hWidth := by
  have hs := build_size p.initial_build
  simp only [List.length_append, List.length_singleton] at hs
  have hWidth : 0 < p.initial.size := by omega
  refine ⟨hWidth, congrArg representation.labels (Fin.ext ?_)⟩
  change g.lower.1.val = p.initial.size - 1
  rw [g.lower_column, hs]
  omega

/-- The full initial reservoir has the actual original prefix as both
its current graph and complete internal reserve. Lower last-column edges
and the actual deleted control are represented by the given old labels. -/
theorem initial_reservoir (g : RootGeometry p) {D : Nat}
    (representation : KeyRepresentation p.initial_valid.toOrdered D) :
    Splice.ReservoirState (p.initialSpliceFacts D) (p.initialSpliceFacts D)
      (g.initialSpliceVirtualFacts D) (g.initialSpliceControl D)
      (p.initialSpliceLabels representation) (representation.labels g.lower.1) := by
  let preserved := PreservesColumns.pop_prefix p.initial
  let old := representation.restrict preserved p.initial_valid.pop.toOrdered
  let fresh := p.initialSpliceLabels representation
  have hLabels (column : Fin (Frame.ofMountain p.initial.pop).width) :
      fresh (Fin.cast p.initial_pop_size column) = old.labels column := rfl
  have hGraph : Reflection.InternalHolds (KeyReflection.vectorSyntax (D + 1))
      (KeyReflection.R (D + 1)) (p.initialSpliceFacts D) fresh := by
    intro atom hAtom
    obtain ⟨edge, _, rfl⟩ := List.mem_map.mp hAtom
    exact Splice.holds_map (Fin.cast p.initial_pop_size) (Splice.fin_cast_strictMono _)
      (edge.atom p.initial_valid.pop.toOrdered D) old.labels fresh hLabels (old.edges edge)
  refine ⟨old.strictMono.comp (Splice.fin_cast_strictMono p.initial_pop_size.symm), ?_,
    hGraph, hGraph, ?_, ?_⟩
  · intro column
    rw [p.initialSpliceLabels_value]
    apply representation.strictMono
    change column.val < g.lower.1.val
    rw [g.lower_column]
    exact column.isLt
  · intro atom hAtom
    obtain ⟨edge, rfl⟩ := (g.mem_initialSpliceVirtualFacts_iff D atom).mp hAtom
    apply Splice.top_holds_map (Fin.cast p.initial_pop_size) (g.lowerAtom D edge)
      old.labels fresh hLabels
    have hEval := edge.val.topAtom_key_eval p.initial_valid.toOrdered D p.initial.pop.size
      (edge.property.1.trans p.initial_pop_size.symm) preserved.size_le representation.labels
    change Keys.eval (g.lowerAtom D edge).key old.labels = _ at hEval
    change Model.R (D + 1) (Keys.eval (g.lowerAtom D edge).key old.labels) _ _
    rw [hEval]
    have hChild : edge.val.lower.1 = g.lower.1 := Fin.ext (edge.property.1.trans g.lower_column.symm)
    have h := representation.edges edge.val
    rw [hChild] at h
    exact h
  · apply Splice.top_holds_map (Fin.cast p.initial_pop_size) (g.controlAtom D)
      old.labels fresh hLabels
    have hEval := g.controlEdge.topAtom_key_eval p.initial_valid.toOrdered D p.initial.pop.size
      (g.lower_column.trans p.initial_pop_size.symm) preserved.size_le representation.labels
    change Keys.eval (g.controlAtom D).key old.labels = _ at hEval
    change Model.R (D + 1) (Keys.eval (g.controlAtom D).key old.labels) _ _
    rw [hEval]
    exact representation.edges g.controlEdge

/-- The same base state at the actual zero-block dimensions used by the
iterated splice theorem. Every listed graph edge is an actual prefix edge. -/
theorem zero_reservoir (g : RootGeometry p) (hLast : 1 < last) {D : Nat}
    (representation : KeyRepresentation p.initial_valid.toOrdered D) :
    Splice.ReservoirState (p.spliceGraph hLast D 0) (p.spliceFacts D 0)
      (g.spliceVirtualFacts D 0) (g.spliceControl D 0)
      (p.zeroSpliceLabels representation) (representation.labels g.lower.1) := by
  have hSize : front.length = Splice.blockWidth front.length p.root.column 0 := by
    simp [Splice.blockWidth]
  have hMap : Splice.blockSource p.root_before_last 0 = Fin.cast hSize := by
    funext column
    exact Fin.ext (Splice.blockSource_zero p.root_before_last column)
  have hState := (g.initial_reservoir representation).cast hSize
  have hAtomMap : Splice.mapAtom (Splice.blockSource p.root_before_last 0)
      (Splice.blockSource_strictMono p.root_before_last 0) =
      (Splice.mapAtom (Fin.cast hSize) (Splice.fin_cast_strictMono _) :
        Model.InternalAtom (D + 1) front.length → _) := by
    funext atom
    exact mapAtom_eq_of_pointwise _ _ _ _ (congrFun hMap) atom
  rw [p.spliceGraph_zero hLast D hSize]
  unfold Preparation.spliceFacts spliceVirtualFacts spliceControl
  rw [hAtomMap, hMap]
  exact hState

end RootGeometry
end OmegaY.Expansion

#print axioms OmegaY.Expansion.RootGeometry.initial_reservoir
#print axioms OmegaY.Expansion.Preparation.spliceGraph_zero
#print axioms OmegaY.Expansion.RootGeometry.zero_reservoir
