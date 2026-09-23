/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinalPhysicalMarkerRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PhysicalRootNondirect
import OmegaY.Expansion.ActualNondirectBlocker
import OmegaY.Expansion.FinalActualBlockerValue

/-!
# Physical-marker recognition in the actual final output

An executed origin supplies the correct earlier block and the just-finished
column. Its numerical search is transported through complete preservation,
including final truncation. The effective comparison node is proved to be
in the same final column and no lower than the physical current node.
Consequently higher-node induction is only restricted, never used at the
current node. The local helper isolates the copied-value comparison; the
final theorem supplies it from complete actual value transport. Only the
nondirect nonmarker class remains in the subsequent search reduction.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

/-- The complete final-node interface to the physical criterion. Neither
the intermediate comparison packet nor either target position is an input.
The two geometric conclusions allow the final strict-left/higher induction
hypotheses to be used at the effective comparison endpoints. -/
theorem physical_comparison_final (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (physical : PhysicalMarkerRead execution.copy)
    (hMarked : BucketMem p.marked execution.source.1.val (Frame.ref execution.source))
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hRef : Frame.ref node = physical.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    ∃ comparison : AnySourceBlockerPacket p origin.block origin.start origin.references
        execution.source parent (origin.before.push origin.column),
      let finalComparison := comparison.extend origin.preserved
      finalComparison.pair.u.1 = node.1 ∧
      (Frame.ofMountain result).height node ≤ (Frame.ofMountain result).height finalComparison.pair.u ∧
      ((Frame.ofMountain result).value finalComparison.pair.u ≤ (Frame.ofMountain result).value finalComparison.pair.z →
        (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node) := by
  have hLegal := build_success_legal p.initial_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hBefore : execution.source.1.val < origin.sourceColumn + 1 := by
    rw [execution.source_column]
    omega
  rcases origin.after_state.recorded_any_last_blocker origin.after_history hLast origin.start_run
      hParent execution.copy.state.next_lower hBefore with hDirect | hPacket
  · exact (hNondirect hDirect).elim
  · obtain ⟨comparison⟩ := hPacket
    let finalComparison := comparison.extend origin.preserved
    obtain ⟨localPhysical⟩ := comparison.pair.uCopy.physical_marker_read hMarked
    let finalPhysical : PhysicalMarkerRead finalComparison.pair.uCopy := {
      index := localPhysical.index
      cell := localPhysical.cell
      output_at := localPhysical.output_at
      source_row := localPhysical.source_row }
    have hPhysicalRef : localPhysical.outputRef = physical.outputRef :=
      finalPhysical.unique_ref physical hValid
    have hLocalLeft : ∀ (current father : (Frame.ofMountain (origin.before.push origin.column)).Node),
        current.1.val < localPhysical.outputRef.column → Real current →
        (Frame.ofMountain (origin.before.push origin.column)).rawParent current = some father →
          (Frame.ofMountain (origin.before.push origin.column)).P current = some father := by
      intro current father hColumn hReal hRaw
      have hFinalColumn : (origin.preserved.mapNode current).1.val < node.1.val := by
        rw [origin.preserved.mapNode_column]
        have hRefColumn := congrArg Ref.column hRef
        have hPhysicalColumn := congrArg Ref.column hPhysicalRef
        change node.1.val = physical.outputRef.column at hRefColumn
        omega
      have hP := hLeft (origin.preserved.mapNode current) (origin.preserved.mapNode father)
        hFinalColumn (origin.preserved.mapNode_real hReal) (origin.preserved.mapNode_rawParent hRaw)
      have hFind := (Executable.findParent_ref_iff hValid.toOrdered _ _).mpr hP
      rw [origin.preserved.mapNode_ref, origin.preserved.mapNode_ref,
        origin.preserved.findParent current.1.isLt] at hFind
      exact (Executable.findParent_ref_iff origin.after_state.ambient_valid.toOrdered current father).mp hFind
    obtain ⟨fatherRef, hEdge, recognize⟩ := comparison.physical_comparison_criterion_all
      origin.after_state origin.after_history hLast origin.start_run localPhysical hMarked hBefore hLocalLeft
    have hCopyUnique := finalComparison.pair.uCopy.unique execution.copy
    have hEffectiveRef : Frame.ref finalComparison.pair.u = execution.copy.outputRef :=
      finalComparison.pair.u_ref.trans hCopyUnique.1
    have hColumn : finalComparison.pair.u.1 = node.1 := Fin.ext
      ((congrArg Ref.column hEffectiveRef).trans (congrArg Ref.column hRef).symm)
    have hNodeCell : (Frame.ofMountain result).cell node = physical.cell := Except.ok.inj
      ((Canonical.cellAt_of_frame_node result node).symm.trans
        (by simpa only [hRef] using physical.output_read))
    have hEffectiveCell : (Frame.ofMountain result).cell finalComparison.pair.u = execution.copy.read.outputCell :=
      finalComparison.pair.u_cell.trans hCopyUnique.2
    have hHeight : (Frame.ofMountain result).height node ≤ (Frame.ofMountain result).height finalComparison.pair.u := by
      change ((Frame.ofMountain result).cell node).row ≤ ((Frame.ofMountain result).cell finalComparison.pair.u).row
      rw [hNodeCell, hEffectiveCell, physical.source_row]
      exact execution.copy.read.source_row_le_output
    refine ⟨comparison, hColumn, hHeight, ?_⟩
    intro hBarrier
    have hFound := recognize ((comparison.extend_barrier_iff origin.preserved).mp hBarrier)
    have hBound : localPhysical.outputRef.column < (origin.before.push origin.column).size :=
      (Array.getElem?_eq_some_iff.mp (Canonical.cellAt_ok_iff.mp localPhysical.output_read).choose_spec.1).1
    have hFinalFound : Canonical.findParent result (Frame.ref node) = .ok fatherRef := by
      rw [hRef, ← hPhysicalRef, origin.preserved.findParent hBound]
      exact hFound
    have hFinalEdge := hEdge.preserve origin.preserved
    have hFinalEdgeRead := hFinalEdge
    obtain ⟨_, _, _, _, _, _, hParentRead⟩ := hFinalEdgeRead
    obtain ⟨father, hFatherRef, _⟩ := Canonical.frame_node_of_cellAt hParentRead
    have hRaw := hFinalEdge.rawParent (hRef.trans hPhysicalRef.symm) hFatherRef
    have hP := (Executable.findParent_ref_iff hValid.toOrdered node father).mp
      (by simpa only [hFatherRef] using hFinalFound)
    exact hRaw.trans hP.symm

/-- Complete final physical-marker recognition. The copied comparison is
supplied by actual value transport, using induction only strictly left and
strictly above the original physical node. No value/word comparison or
search correctness at the current node is an input. -/
theorem physical_recognize_final (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (physical : PhysicalMarkerRead execution.copy)
    (hMarked : BucketMem p.marked execution.source.1.val (Frame.ref execution.source))
    {parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hRef : Frame.ref node = physical.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father)
    (hHigher : ∀ (current father : (Frame.ofMountain result).Node), current.1 = node.1 →
      (Frame.ofMountain result).height node < (Frame.ofMountain result).height current →
      Real current → (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  obtain ⟨comparison, hColumn, hHeight, recognize⟩ := execution.physical_comparison_final
    hLast hRun physical hMarked hParent hNondirect hRef hLeft
  have hBefore : execution.source.1.val < origin.sourceColumn + 1 := by
    rw [execution.source_column]
    omega
  apply recognize
  apply origin.after_state.preserved_blocker_barrier origin.after_history hLast origin.start_run
    comparison hBefore origin.preserved (build_success_legal p.initial_build) hRun
  · intro current father hCurrentColumn hReal hRaw
    exact hLeft current father (by simpa only [hColumn] using hCurrentColumn) hReal hRaw
  · intro current father hCurrentColumn hCurrentHeight hReal hRaw
    exact hHigher current father (hCurrentColumn.trans hColumn)
      (hHeight.trans_lt hCurrentHeight) hReal hRaw

end ExecutedNodeCopy

/-- All physical origins are now a proved local search handler, including
root-parent, raised/stationary, direct/nondirect and preserved earlier-block
cases. No height threshold beyond the handler's stipulated scope is used. -/
theorem Preparation.low_physical_marker_step
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    p.LowRecognitionOn result (PhysicalMarkerAt p result) := by
  rintro current father _ _ _ ⟨origin, execution, physical, hSourceReal, hMarked, hRef⟩ hRaw hLeft hHigher
  obtain ⟨parent, hParent, _, _⟩ := p.real_marker_parent hSourceReal hMarked
  by_cases hDirect : (Frame.ofMountain p.reduced).Q execution.source = some parent
  · exact (physical.recognize_direct_all hLast hRun hMarked hParent hDirect hRef).symm.trans hRaw
  · exact (execution.physical_recognize_final hLast hRun physical hMarked hParent hDirect hRef hLeft hHigher).symm.trans hRaw

/-- The only source-origin class still requiring a numerical handler:
an actual nonmarker whose source search skips candidates. The full executed
packet is retained, including its true earlier-block history. -/
def NondirectNonmarkerAt {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (node : (Frame.ofMountain result).Node) : Prop :=
  ∃ (origin : CopiedNodeOrigin p result node) (execution : ExecutedNodeCopy origin)
    (parent : (Frame.ofMountain p.reduced).Node),
    (Frame.ofMountain p.reduced).P execution.source = some parent ∧
    (Frame.ofMountain p.reduced).Q execution.source ≠ some parent ∧
    ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source) ∧
    Frame.ref node = execution.copy.outputRef

theorem Preparation.low_copied_step_of_nondirect_nonmarker
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hNonmarker : p.LowRecognitionOn result (NondirectNonmarkerAt p result)) :
    p.LowCopiedRecognitionStep result := by
  apply p.low_copied_step_of_nondirect_source hLast hCopies hRun
  rintro current father hColumn hReal hLow ⟨origin, execution, parent, hParent, hNondirect, hBranch⟩ hRaw hLeft hHigher
  rcases hBranch with ⟨hUnmarked, hRef⟩ | ⟨physical, hMarked, hRef⟩
  · exact hNonmarker current father hColumn hReal hLow
      ⟨origin, execution, parent, hParent, hNondirect, hUnmarked, hRef⟩ hRaw hLeft hHigher
  · exact (execution.physical_recognize_final hLast hRun physical hMarked hParent hNondirect hRef hLeft hHigher).symm.trans hRaw

/-- Only the explicitly stated nondirect nonmarker handler remains open.
All physical marker and reference-gap cases are actual proved branches. -/
theorem Preparation.rawParentSearch_of_low_nondirect_nonmarker
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hNonmarker : p.LowRecognitionOn result (NondirectNonmarkerAt p result)) :
    (Frame.ofMountain result).RawParentSearch :=
  p.rawParentSearch_of_low_copied_step hLast hCopies hRun
    (p.low_copied_step_of_nondirect_nonmarker hLast hCopies hRun hNonmarker)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.physical_comparison_final
#print axioms OmegaY.Expansion.ExecutedNodeCopy.physical_recognize_final
#print axioms OmegaY.Expansion.Preparation.low_physical_marker_step
#print axioms OmegaY.Expansion.Preparation.low_copied_step_of_nondirect_nonmarker
#print axioms OmegaY.Expansion.Preparation.rawParentSearch_of_low_nondirect_nonmarker
