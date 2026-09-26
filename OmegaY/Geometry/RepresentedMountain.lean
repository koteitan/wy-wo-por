/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Geometry/RepresentedMountain.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PreservedMountainKeys
import OmegaY.Expansion.Totality
import OmegaY.Expansion.FinalHighEventSampling

/-!
# Ordinal representations of actual stored mountain edges

The representation reads the finite keys computed from the entire stored
parent diagram. Initial representations exist without a graph oracle.
Restricting any representation to a genuine complete prefix preserves all
edge relations. A proper prefix is represented strictly below the old last
label; this proves the real deletion branches of expansion descent.
The positive-copy representation construction remains a separate obligation.
-/

namespace OmegaY.Geometry.Frame

structure KeyRepresentation {F : Frame} (hF : F.Ordered) (D : Nat) where
  labels : Fin F.width → Model.Label
  strictMono : StrictMono labels
  bounded : ∀ column, labels column < Reflection.OrdinalSupply.top
  edges : ∀ edge : RealStoredEdge F,
    Model.R (D + 1) (Keys.eval (edge.keyTemplate hF D) labels)
      (labels edge.parent.1) (labels edge.lower.1)

theorem keyRepresentation_exists {F : Frame} (hF : F.Ordered) (D : Nat) :
    Nonempty (KeyRepresentation hF D) := by
  obtain ⟨beta, hBeta, f, hMono, hBound, hEdges⟩ := actual_keys_initially_represented hF D
  exact ⟨⟨f, hMono, fun i => (hBound i).trans hBeta, hEdges⟩⟩

namespace KeyRepresentation

open Canonical Expansion

variable {before after : Mountain} {D : Nat}
  {hAfter : (Frame.ofMountain after).Ordered}
  (representation : KeyRepresentation hAfter D)

noncomputable def restrict (preserved : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) : KeyRepresentation hBefore D where
  labels := representation.labels ∘ preserved.keyColumn
  strictMono := representation.strictMono.comp preserved.keyColumn_strictMono
  bounded := fun i => representation.bounded (preserved.keyColumn i)
  edges := by
    intro edge
    have he := representation.edges (preserved.storedEdge edge)
    have hKey := preserved.storedEdge_key_eval (Label := Model.Label)
      hBefore hAfter edge D representation.labels
    rw [hKey] at he
    have hp : (preserved.storedEdge edge).parent.1 = preserved.keyColumn edge.parent.1 :=
      Fin.ext (preserved.mapNode_column edge.parent)
    have hc : (preserved.storedEdge edge).lower.1 = preserved.keyColumn edge.lower.1 :=
      Fin.ext (preserved.mapNode_column edge.lower)
    rw [hp, hc] at he
    exact he

def lastLabel (hNonempty : 0 < after.size) : Model.Label :=
  representation.labels ⟨after.size - 1, by change after.size - 1 < after.size; omega⟩

theorem restrict_below_last (preserved : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hProper : before.size < after.size)
    (column : Fin before.size) :
    (representation.restrict preserved hBefore).labels column <
      representation.lastLabel (by omega) := by
  apply representation.strictMono
  change column.val < after.size - 1
  have hi := column.isLt
  omega

end KeyRepresentation
end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame

/-- From every old representation, the actual nonempty deletion branch
returns a representation all of whose labels are below the old last label.
This includes deletion to the empty mountain, with a vacuous new-label bound.
It makes no assertion about a positive-copy branch.
-/
theorem expandDiagram_trivial_representation_descent
    {input : List Nat} {initial result : Mountain} {copies D : Nat}
    (hBuild : Canonical.build input = .ok initial) (hNonempty : input ≠ [])
    (hRun : expandDiagram input copies = .ok result)
    (hTrivial : input.getLast? = some 1 ∨ copies = 0)
    (representation : KeyRepresentation (build_normal_of_success hBuild).toOrdered D) :
    ∃ (hInitialWidth : 0 < initial.size)
      (fresh : KeyRepresentation
        (expandDiagram_valid_of_success (build_success_legal hBuild) hRun).toOrdered D),
      ∀ column, fresh.labels column < representation.lastLabel hInitialWidth := by
  have hActual : expandDiagram input copies = .ok initial.pop := by
    simp [expandDiagram, hBuild, Except.mapError, hTrivial]
  have he : result = initial.pop := Except.ok.inj (hRun.symm.trans hActual)
  subst result
  have hWidth : 0 < initial.size := by
    rw [build_size hBuild]
    exact List.length_pos_iff.mpr hNonempty
  let preserved := PreservesColumns.pop_prefix initial
  let hOrdered := (expandDiagram_valid_of_success (build_success_legal hBuild) hRun).toOrdered
  refine ⟨hWidth, representation.restrict preserved hOrdered, ?_⟩
  intro column
  exact representation.restrict_below_last preserved hOrdered
    (by simp only [Array.size_pop]; omega) column

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.keyRepresentation_exists
#print axioms OmegaY.Geometry.Frame.KeyRepresentation.restrict
#print axioms OmegaY.Geometry.Frame.KeyRepresentation.restrict_below_last
#print axioms OmegaY.Expansion.expandDiagram_trivial_representation_descent
