/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNondirectBlocker.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNondirectSearchReduction
import OmegaY.Expansion.PreservedAnyLastBlocker
import OmegaY.Expansion.PreservedBlockerPacket
import OmegaY.Expansion.ActualEffectiveRecognition
import OmegaY.Expansion.EffectiveOccurrenceUnique

/-!
# Actual last-blocker packets for the remaining nondirect source cases

The final node's executed column packet supplies the actual after-state,
source search and final preservation. Neither a chosen blocker nor a
chosen source/target comparison packet is given by the caller.

The universal packet records source Q and its actual parent-record path.
It does not claim that an unchanged source blocker lies on the new Q
path. For a nonmarker whose source parent is strictly right of the root,
that new-path issue is already proved: the final recognition criterion
below leaves only the displayed actual copied-value inequality.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

/-- The actual source search and every source-parent position are covered.
The source path, source inequality and genuine source upper event are
available from the returned packet; no target comparison is inferred. -/
theorem any_last_blocker (hLast : 1 < last)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent) :
    ∃ comparison : AnySourceBlockerPacket p origin.block origin.start origin.references
        execution.source parent result,
      Frame.ref comparison.pair.u = execution.copy.outputRef := by
  have hBefore : execution.source.1.val < origin.sourceColumn + 1 := by
    rw [execution.source_column]
    omega
  rcases origin.after_state.recorded_any_last_blocker origin.after_history hLast origin.start_run
      hParent execution.copy.state.next_lower hBefore with hDirect | hPacket
  · exact (hNondirect hDirect).elim
  · obtain ⟨packet⟩ := hPacket
    let comparison := packet.extend origin.preserved
    exact ⟨comparison, comparison.pair.u_ref.trans (comparison.pair.uCopy.unique execution.copy).1⟩

/-- In the copied-parent nonmarker branch, the source-selected record path
also has an actual copied raw path. Its final current node is the caller's
original node, not a merely same-row substitute. -/
theorem nonmarker_last_blocker (hLast : 1 < last)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hParentRight : p.root.column < parent.1.val)
    (hUnmarked : ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source))
    (hRef : Frame.ref node = execution.copy.outputRef) :
    ∃ comparison : SourceBlockerCopyPacket p origin.block origin.start origin.references
        execution.source parent result,
      comparison.pair.u = node := by
  have hBefore : execution.source.1.val < origin.sourceColumn + 1 := by
    rw [execution.source_column]
    omega
  rcases origin.after_state.recorded_nonmarker_last_blocker origin.after_history hLast
      hParent hParentRight hBefore (execution.unmarked_indices hUnmarked) with hDirect | hPacket
  · exact (hNondirect hDirect).elim
  · obtain ⟨packet⟩ := hPacket
    let comparison := packet.extend origin.preserved
    exact ⟨comparison, Executable.ref_injective _
      (comparison.pair.u_ref.trans ((comparison.pair.uCopy.unique execution.copy).1.trans hRef.symm))⟩

/-- The precise remaining comparison for the actual copied-parent,
nonmarker search. Actual Q, every record edge, the last blocker, and strict
smallness of the designated parent are derived inside the implication.
Only strict-left numerical recognition and this copied-value inequality
are needed; higher-node recognition is reserved for proving the inequality.
-/
theorem nonmarker_comparison_criterion (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hParentRight : p.root.column < parent.1.val)
    (hUnmarked : ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source))
    (hRef : Frame.ref node = execution.copy.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    ∃ comparison : SourceBlockerCopyPacket p origin.block origin.start origin.references
        execution.source parent result,
      comparison.pair.u = node ∧
      ((Frame.ofMountain result).value node ≤ (Frame.ofMountain result).value comparison.pair.z →
        (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node) := by
  obtain ⟨comparison, hCurrent⟩ := execution.nonmarker_last_blocker
    hLast hParent hNondirect hParentRight hUnmarked hRef
  refine ⟨comparison, hCurrent, ?_⟩
  intro hBarrier
  have hLegal := build_success_legal p.initial_build
  have hP := comparison.recognize_of_nonmarker_barrier hLast
    (expandDiagram_valid_of_success hLegal hRun) (OmegaY.Expansion.expandDiagram_equations hLegal hRun).1
    (by simpa only [hCurrent] using hLeft) (execution.unmarked_indices hUnmarked) hParentRight
    (by simpa only [hCurrent] using hBarrier)
  have hRaw := comparison.pair.u_parent
  rw [hCurrent] at hRaw hP
  exact hRaw.trans hP.symm

end ExecutedNodeCopy

/-- Instantiation of the universal packet from the precise remaining
origin predicate. The effective current is deliberately distinguished from
a physical-marker target; their equality is not assumed. -/
theorem NondirectSourceAt.actual_comparison
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node}
    (hOrigin : NondirectSourceAt p result node) (hLast : 1 < last) :
    ∃ (origin : CopiedNodeOrigin p result node) (execution : ExecutedNodeCopy origin)
      (parent : (Frame.ofMountain p.reduced).Node)
      (comparison : AnySourceBlockerPacket p origin.block origin.start origin.references
        execution.source parent result),
      (Frame.ofMountain p.reduced).P execution.source = some parent ∧
      (Frame.ofMountain p.reduced).Q execution.source ≠ some parent ∧
      Frame.ref comparison.pair.u = execution.copy.outputRef ∧
      ((¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source) ∧
          Frame.ref node = execution.copy.outputRef) ∨
        ∃ physical : PhysicalMarkerRead execution.copy,
          BucketMem p.marked execution.source.1.val (Frame.ref execution.source) ∧
          Frame.ref node = physical.outputRef) := by
  obtain ⟨origin, execution, parent, hParent, hNondirect, hBranch⟩ := hOrigin
  obtain ⟨comparison, hRef⟩ := execution.any_last_blocker hLast hParent hNondirect
  exact ⟨origin, execution, parent, comparison, hParent, hNondirect, hRef, hBranch⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.any_last_blocker
#print axioms OmegaY.Expansion.ExecutedNodeCopy.nonmarker_last_blocker
#print axioms OmegaY.Expansion.ExecutedNodeCopy.nonmarker_comparison_criterion
#print axioms OmegaY.Expansion.NondirectSourceAt.actual_comparison
