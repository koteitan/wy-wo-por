/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNondirectSearchReduction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowPhysicalCases

/-!
# The remaining low search step is a genuine nondirect source search

Actual source provenance, all reference-gap nodes, parentless source tops
and every direct source Q=P case are discharged internally. Physical
markers include the root-column parent branch. The remaining predicate
retains the exact executed block/column packet and is restricted to source
searches which must skip at least one candidate. The handler for that
predicate remains unproved; no target comparison is asserted here.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {packet : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy packet)

/-- The effective occurrence in the actual just-completed column, before
its preservation into the caller's final graph. -/
def local_copy : EffectiveCopyOccurrence p packet.block packet.start packet.references
    execution.source (packet.before.push packet.column) := {
  execution.copy with
  preserved := by
    rw [execution.before_eq, execution.column_eq]
    exact fun _ _ => rfl }

theorem unmarked_indices
    (hUnmarked : ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source)) :
    execution.source.2.val ∉ (p.marked[execution.source.1.val]?.getD []).map Ref.index := by
  intro hIndex
  obtain ⟨marker, hm, hMarkerIndex⟩ := List.mem_map.mp hIndex
  have hColumn := execution.copy.data.marker_columns marker hm
  have hRef : marker = Frame.ref execution.source := congrArg₂ Ref.mk hColumn hMarkerIndex
  exact hUnmarked (by simpa only [BucketMem, hRef] using hm)

theorem source_real_of_unmarked
    (hUnmarked : ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source)) :
    Real execution.source := by
  have hIndex := execution.unmarked_indices hUnmarked
  by_contra hn
  have hi : execution.source.2.val = 0 := by
    change ¬ 0 < execution.source.2.val at hn
    omega
  apply hIndex
  rw [hi]
  exact List.mem_map.mpr ⟨⟨execution.source.1.val, 0⟩,
    execution.copy.data.phantom_marker, rfl⟩

/-- The direct source theorem is instantiated in the recorded after-state
and carried through actual final preservation. The caller supplies no
intermediate history, chosen reference map or copied-data certificate. -/
theorem nonmarker_direct (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hUnmarked : ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source))
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hDirect : (Frame.ofMountain p.reduced).Q execution.source = some parent)
    (hRef : Frame.ref node = execution.copy.outputRef) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  have hBefore : execution.source.1.val < packet.sourceColumn + 1 := by
    rw [execution.source_column]
    omega
  exact packet.after_state.nonmarker_direct_rawParent_eq_P_preserved
    packet.after_history hLast packet.start_run packet.preserved
    (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered
    execution.local_copy hParent hDirect hBefore (execution.unmarked_indices hUnmarked) hRef

end ExecutedNodeCopy

/-- The unresolved source classes, now restricted to actual nondirect
searches. The execution packet retains both histories, the start run and
the exact final preservation. This predicate contains no target inequality,
target-parent recognition, or copied normality hypothesis. -/
def NondirectSourceAt {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (node : (Frame.ofMountain result).Node) : Prop :=
  ∃ (packet : CopiedNodeOrigin p result node) (execution : ExecutedNodeCopy packet)
    (parent : (Frame.ofMountain p.reduced).Node),
    (Frame.ofMountain p.reduced).P execution.source = some parent ∧
    (Frame.ofMountain p.reduced).Q execution.source ≠ some parent ∧
      ((¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source) ∧
        Frame.ref node = execution.copy.outputRef) ∨
       ∃ physical : PhysicalMarkerRead execution.copy,
        BucketMem p.marked execution.source.1.val (Frame.ref execution.source) ∧
        Frame.ref node = physical.outputRef)

/-- All alternatives are obtained from the real final run. The first
alternative is a parentless copied top, which cannot occur in a some-raw-
parent recognition obligation. The second is already numerically proved. -/
theorem Preparation.copied_node_nondirect_cases
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {node : (Frame.ofMountain result).Node}
    (hColumn : p.reduced.size ≤ node.1.val) (hReal : Real node) :
    (Frame.ofMountain result).rawParent node = none ∨
      (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node ∨
      NondirectSourceAt p result node := by
  rcases p.copied_node_recognition_cases hLast hCopies hRun hColumn hReal with
    hKnown | ⟨packet, execution, hUnmarked, hRef⟩ | ⟨packet, execution, physical, hSourceReal, hMarked, hRef⟩
  · exact Or.inr (Or.inl hKnown)
  · cases hParent : (Frame.ofMountain p.reduced).P execution.source with
    | none =>
        exact Or.inl (execution.copy.rawParent_none_of_source_parent_none hLast
          (execution.source_real_of_unmarked hUnmarked) hParent hRef)
    | some parent =>
        by_cases hDirect : (Frame.ofMountain p.reduced).Q execution.source = some parent
        · exact Or.inr (Or.inl (execution.nonmarker_direct hLast hRun hUnmarked hParent hDirect hRef))
        · exact Or.inr (Or.inr ⟨packet, execution, parent, hParent, hDirect,
            Or.inl ⟨hUnmarked, hRef⟩⟩)
  · obtain ⟨parent, hParent, _, _⟩ := p.real_marker_parent hSourceReal hMarked
    by_cases hDirect : (Frame.ofMountain p.reduced).Q execution.source = some parent
    · exact Or.inr (Or.inl (physical.recognize_direct_all hLast hRun hMarked hParent hDirect hRef))
    · exact Or.inr (Or.inr ⟨packet, execution, parent, hParent, hDirect,
        Or.inr ⟨physical, hMarked, hRef⟩⟩)

theorem Preparation.low_copied_step_of_nondirect_source
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hNondirect : p.LowRecognitionOn result (NondirectSourceAt p result)) :
    p.LowCopiedRecognitionStep result := by
  intro current father hColumn hReal hLow hRaw hLeft hHigher
  rcases p.copied_node_nondirect_cases hLast hCopies hRun hColumn hReal with
    hNone | hKnown | hOrigin
  · rw [hNone] at hRaw
    cases hRaw
  · exact hKnown.symm.trans hRaw
  · exact hNondirect current father hColumn hReal hLow hOrigin hRaw hLeft hHigher

/-- Conditional on the one still-open low nondirect recognition handler.
No reference-gap, physical-direct, nonmarker-direct or source-top handler
remains, and neither strict induction hypothesis is assumed globally. -/
theorem Preparation.rawParentSearch_of_low_nondirect_source
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hNondirect : p.LowRecognitionOn result (NondirectSourceAt p result)) :
    (Frame.ofMountain result).RawParentSearch :=
  p.rawParentSearch_of_low_copied_step hLast hCopies hRun
    (p.low_copied_step_of_nondirect_source hLast hCopies hRun hNondirect)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.unmarked_indices
#print axioms OmegaY.Expansion.ExecutedNodeCopy.source_real_of_unmarked
#print axioms OmegaY.Expansion.ExecutedNodeCopy.nonmarker_direct
#print axioms OmegaY.Expansion.Preparation.copied_node_nondirect_cases
#print axioms OmegaY.Expansion.Preparation.low_copied_step_of_nondirect_source
#print axioms OmegaY.Expansion.Preparation.rawParentSearch_of_low_nondirect_source
