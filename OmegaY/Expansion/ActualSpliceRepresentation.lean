/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSpliceRepresentation.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSpliceReservoirs
import OmegaY.Expansion.ActualInitialReservoir
import OmegaY.Expansion.ActualSpliceGeometry

/-!
Actual finite block graphs instantiate the complete reservoir iteration.
The intermediate lemmas display the finite classification interface.
The final theorems discharge it using the actual retained/boundary/copy
classification. The old representation supplies the initial state, and
the source mountain supplies every demand comparison. Finally the finite
graph's relations become the full actual mountain representation.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace Preparation

variable {front : List Nat} {last : Nat} (p : Preparation front last)

/-- Representation of the enumerated graph is representation of every
real stored edge of the actual mountain; no graph-completeness oracle is
needed because `spliceGraph` enumerates all such edges. -/
noncomputable def representationOfSpliceGraph (hLast : 1 < last) (D block : Nat)
    (labels : Fin (Splice.blockWidth front.length p.root.column block) → Model.Label)
    (beta : Model.Label) (hMono : StrictMono labels) (hBound : Reflection.Bounded labels beta)
    (hBeta : beta < Reflection.OrdinalSupply.top)
    (hGraph : Reflection.InternalHolds (KeyReflection.vectorSyntax (D + 1))
      (KeyReflection.R (D + 1)) (p.spliceGraph hLast D block) labels) :
    KeyRepresentation (p.spliceMountain_valid hLast block).toOrdered D where
  labels := fun column => labels (Fin.cast (p.spliceMountain_size hLast block) column)
  strictMono := hMono.comp (Splice.fin_cast_strictMono _)
  bounded := fun column => (hBound _).trans hBeta
  edges := by
    intro edge
    have he := hGraph (p.spliceEdgeAtom hLast D block edge) (p.spliceEdgeAtom_mem hLast D block edge)
    change Model.R (D + 1)
      (Keys.eval (Keys.relabel (edge.keyTemplate (p.spliceMountain_valid hLast block).toOrdered D)
        (Fin.cast (p.spliceMountain_size hLast block))) labels)
      (labels (Fin.cast (p.spliceMountain_size hLast block) edge.parent.1))
      (labels (Fin.cast (p.spliceMountain_size hLast block) edge.lower.1)) at he
    rw [Keys.eval_relabel] at he
    exact he

end Preparation

namespace RootGeometry

variable {front : List Nat} {last : Nat} {p : Preparation front last}

/-- The remaining interface contains only actual edge and finite-key
classification, with no ordinal labels or representation predicate. -/
def SpliceGeometry (g : RootGeometry p) (hLast : 1 < last) (D : Nat) : Prop :=
  ∀ block (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1)))),
    Splice.ReservoirClassified (Splice.blockCut p.root_before_last block)
      (p.spliceGraph hLast D block) (p.spliceFacts D block) (g.spliceVirtualFacts D block)
      (p.spliceLocalEdgeAtom hLast D block edge)

theorem SpliceGeometry.block_geometry {g : RootGeometry p} {hLast : 1 < last} {D : Nat}
    (hClass : g.SpliceGeometry hLast D) (block : Nat) :
    Splice.BlockReservoirGeometry p.root_before_last block
      (p.spliceGraph hLast D block) (p.spliceFacts D block) (g.spliceVirtualFacts D block)
      (p.spliceGraph hLast D (block + 1)) := by
  intro atom hAtom
  obtain ⟨sourceAtom, hSource, rfl⟩ := List.mem_map.mp hAtom
  obtain ⟨edge, _hEdge, rfl⟩ := List.mem_map.mp hSource
  exact hClass block edge

/-- All actual block graphs receive the full finite reserves, with the
same original last-column label as external bound. No initial-state or
demand-key hypothesis remains at this interface. -/
theorem iterated_actual_reservoirs (g : RootGeometry p) (hLast : 1 < last) {D : Nat}
    (hDimension : MountainKeyDimension p.initial D)
    (old : KeyRepresentation p.initial_valid.toOrdered D)
    (hClass : g.SpliceGeometry hLast D) :
    ∀ block, ∃ labels : Fin (Splice.blockWidth front.length p.root.column block) → Model.Label,
      Splice.ReservoirState (p.spliceGraph hLast D block) (p.spliceFacts D block)
        (g.spliceVirtualFacts D block) (g.spliceControl D block) labels (old.labels g.lower.1) ∧
      (∀ column, labels (Splice.blockSource p.root_before_last block column) =
        p.initialSpliceLabels old column) := by
  intro block
  obtain ⟨labels, hState, hReuse⟩ := Splice.iterated_reservoirs p.root_before_last
    (p.spliceGraph hLast D) (p.initialSpliceFacts D) (g.initialSpliceVirtualFacts D)
    (g.initialSpliceControl D) (g.spliceVirtualFacts D) (p.zeroSpliceLabels old)
    (old.labels g.lower.1) (g.initialSpliceControl_parent D) (g.zero_reservoir hLast old)
    (g.spliceVirtualFacts_self_covered D) (g.spliceVirtualFacts_key_strict hDimension)
    hClass.block_geometry block
  refine ⟨labels, hState, ?_⟩
  intro column
  exact (hReuse column).trans (p.zeroSpliceLabels_source old column)

/-- This returns an actual mountain representation below the old last
label, conditional only on the displayed finite edge classification. -/
theorem represent_spliceMountain (g : RootGeometry p) (hLast : 1 < last) {D : Nat}
    (hDimension : MountainKeyDimension p.initial D)
    (old : KeyRepresentation p.initial_valid.toOrdered D)
    (hClass : g.SpliceGeometry hLast D) (block : Nat) :
    ∃ (hWidth : 0 < p.initial.size)
      (fresh : KeyRepresentation (p.spliceMountain_valid hLast block).toOrdered D),
      ∀ column, fresh.labels column < old.lastLabel hWidth := by
  obtain ⟨labels, hState, _hReuse⟩ := g.iterated_actual_reservoirs hLast hDimension old hClass block
  obtain ⟨hWidth, hBeta⟩ := g.initialSpliceBeta_eq_lastLabel old
  let fresh := p.representationOfSpliceGraph hLast D block labels (old.labels g.lower.1)
    hState.strict hState.bounded (old.bounded g.lower.1) hState.graph
  refine ⟨hWidth, fresh, ?_⟩
  intro column
  change labels (Fin.cast (p.spliceMountain_size hLast block) column) < old.lastLabel hWidth
  exact (hState.bounded _).trans_eq hBeta

/-- Determinism identifies the represented graph with the program's
actual positive-copy output, including its final deletion of the temporary
last column. The finite edge classification is still an explicit input. -/
theorem represent_expansion_of_splice_geometry (g : RootGeometry p) (hLast : 1 < last)
    {D : Nat} (hDimension : MountainKeyDimension p.initial D)
    (old : KeyRepresentation p.initial_valid.toOrdered D)
    (hClass : g.SpliceGeometry hLast D) {copies : Nat} (hCopies : 0 < copies)
    {result : Mountain} (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    ∃ (hWidth : 0 < p.initial.size)
      (fresh : KeyRepresentation
        (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered D),
      ∀ column, fresh.labels column < old.lastLabel hWidth := by
  have he : result = p.spliceMountain hLast copies := Except.ok.inj
    (hRun.symm.trans (p.expandDiagram_eq_spliceMountain hLast hCopies))
  subst result
  exact g.represent_spliceMountain hLast hDimension old hClass copies

/-- Full finite reserves on every actual block, now with every geometric
classification proved from the executable expansion. -/
theorem actual_reservoirs (g : RootGeometry p) (hLast : 1 < last) {D : Nat}
    (hDimension : MountainKeyDimension p.initial D)
    (old : KeyRepresentation p.initial_valid.toOrdered D) :
    ∀ block, ∃ labels : Fin (Splice.blockWidth front.length p.root.column block) → Model.Label,
      Splice.ReservoirState (p.spliceGraph hLast D block) (p.spliceFacts D block)
        (g.spliceVirtualFacts D block) (g.spliceControl D block) labels (old.labels g.lower.1) ∧
      (∀ column, labels (Splice.blockSource p.root_before_last block column) =
        p.initialSpliceLabels old column) :=
  g.iterated_actual_reservoirs hLast hDimension old
    (p.actual_splice_edge_classified g hLast D hDimension)

/-- Genuine positive-copy representation descent for the prepared actual
input. No geometric classification, key comparison, or successor
representation is a hypothesis of this theorem. -/
theorem represent_actual_expansion (g : RootGeometry p) (hLast : 1 < last)
    {D : Nat} (hDimension : MountainKeyDimension p.initial D)
    (old : KeyRepresentation p.initial_valid.toOrdered D)
    {copies : Nat} (hCopies : 0 < copies)
    {result : Mountain} (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    ∃ (hWidth : 0 < p.initial.size)
      (fresh : KeyRepresentation
        (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered D),
      ∀ column, fresh.labels column < old.lastLabel hWidth :=
  g.represent_expansion_of_splice_geometry hLast hDimension old
    (p.actual_splice_edge_classified g hLast D hDimension) hCopies hRun

end RootGeometry
end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.representationOfSpliceGraph
#print axioms OmegaY.Expansion.RootGeometry.iterated_actual_reservoirs
#print axioms OmegaY.Expansion.RootGeometry.represent_expansion_of_splice_geometry
#print axioms OmegaY.Expansion.RootGeometry.actual_reservoirs
#print axioms OmegaY.Expansion.RootGeometry.represent_actual_expansion
