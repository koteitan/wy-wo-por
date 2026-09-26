/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowOriginReduction.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowSearchReduction
import OmegaY.Expansion.ActualReferenceGapRecognition
import OmegaY.Expansion.ActualPhysicalMarkerRecognition
import OmegaY.Expansion.ActualMarkerParentBounds

/-!
# Low-node reduction after recognizing every reference-gap cell

The two remaining predicates describe actual final occurrences, not
abstract source rows or assumed successful searches. Their witnesses are
constructed from the executed column history, including earlier blocks
and preservation through the final pop. No history or copy-data premise is
required by the reduction theorem.

This file does not prove the two remaining numerical handlers. In
particular, identifying a stationary physical marker with its effective
endpoint does not establish the missing low endpoint comparison.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

/-- The effective read is tied to the exact column execution recovered
from the final run. The packet retains the actual start run, both histories
and final preservation; the physical and effective output indices can
still differ. -/
structure ExecutedNodeCopy {front : List Nat} {last : Nat} {p : Preparation front last}
    {result : Mountain} {node : (Frame.ofMountain result).Node}
    (packet : CopiedNodeOrigin p result node) where
  source : (Frame.ofMountain p.reduced).Node
  source_column : source.1.val = packet.sourceColumn
  copy : EffectiveCopyOccurrence p packet.block packet.start packet.references source result
  before_eq : copy.before = packet.before
  column_eq : copy.column = packet.column

/-- An actual nonmarker effective copy at this exact final reference. -/
def NonmarkerCopyAt {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (node : (Frame.ofMountain result).Node) : Prop :=
  ∃ (packet : CopiedNodeOrigin p result node) (execution : ExecutedNodeCopy packet),
    ¬ BucketMem p.marked execution.source.1.val (Frame.ref execution.source) ∧
      Frame.ref node = execution.copy.outputRef

/-- An actual physical marker at this exact final reference. The source
is real, so phantom markers are not left as numerical obligations. -/
def PhysicalMarkerAt {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (node : (Frame.ofMountain result).Node) : Prop :=
  ∃ (packet : CopiedNodeOrigin p result node) (execution : ExecutedNodeCopy packet)
    (physical : PhysicalMarkerRead execution.copy),
    Real execution.source ∧
      BucketMem p.marked execution.source.1.val (Frame.ref execution.source) ∧
      Frame.ref node = physical.outputRef

theorem CopiedNodeOrigin.effective_execution
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    {sourceIndex : Nat} {sourceCell : Cell}
    (read : EffectiveCopyRead packet.data sourceIndex sourceCell packet.column)
    (hIndex : read.outputIndex = node.2.val) :
    ∃ execution : ExecutedNodeCopy packet,
      execution.source.2.val = sourceIndex ∧ Frame.ref node = execution.copy.outputRef := by
  let sourceColumn : Fin (Frame.ofMountain p.reduced).width :=
    ⟨packet.sourceColumn, packet.source_bound⟩
  have hLength : (Frame.ofMountain p.reduced).length sourceColumn = packet.data.sources.size :=
    congrArg Array.size (Array.getElem?_eq_some_iff.mp packet.source_read).2
  have hi : sourceIndex < (Frame.ofMountain p.reduced).length sourceColumn := by
    rw [hLength]
    exact (Array.getElem?_eq_some_iff.mp read.source_at).1
  let source : (Frame.ofMountain p.reduced).Node := ⟨sourceColumn, ⟨sourceIndex, hi⟩⟩
  have hSourceRead : Canonical.cellAt p.reduced (Frame.ref source) = .ok sourceCell :=
    cellAt_ok_iff.mpr ⟨packet.data.sources, packet.source_read, read.source_at⟩
  have hSourceCell : (Frame.ofMountain p.reduced).cell source = sourceCell :=
    Except.ok.inj ((Canonical.cellAt_of_frame_node p.reduced source).symm.trans hSourceRead)
  subst sourceCell
  let copy : EffectiveCopyOccurrence p packet.block packet.start packet.references source result := {
    before := packet.before
    column := packet.column
    state := packet.state
    data := packet.data
    read := read
    preserved := packet.preserved }
  let execution : ExecutedNodeCopy packet := ⟨source, rfl, copy, rfl, rfl⟩
  refine ⟨execution, rfl, ?_⟩
  change (⟨node.1.val, node.2.val⟩ : Ref) = ⟨packet.before.size, read.outputIndex⟩
  exact congrArg₂ Ref.mk packet.target_column.symm hIndex.symm

/-- Inverting the physical constructor supplies the source, its effective
occurrence and the separate physical read. The two output indices need
not coincide. -/
theorem CopiedNodeOrigin.physical_occurrence
    {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
    {node : (Frame.ofMountain result).Node} (packet : CopiedNodeOrigin p result node)
    (hLast : 1 < last) (hValid : MountainValid result) (hReal : Real node)
    {marker : Ref} (hm : marker ∈ packet.data.bucket)
    (hRow : (Frame.ofMountain result).height node =
      (packet.data.marker_data marker hm).current.row) :
    PhysicalMarkerAt p result node := by
  let md := packet.data.marker_data marker hm
  let sourceColumn : Fin (Frame.ofMountain p.reduced).width :=
    ⟨packet.sourceColumn, packet.source_bound⟩
  have hLength : (Frame.ofMountain p.reduced).length sourceColumn = packet.data.sources.size :=
    congrArg Array.size (Array.getElem?_eq_some_iff.mp packet.source_read).2
  have hi : marker.index < (Frame.ofMountain p.reduced).length sourceColumn := by
    rw [hLength]
    exact (Array.getElem?_eq_some_iff.mp md.current_at).1
  let source : (Frame.ofMountain p.reduced).Node := ⟨sourceColumn, ⟨marker.index, hi⟩⟩
  have hSourceRead : Canonical.cellAt p.reduced (Frame.ref source) = .ok md.current :=
    cellAt_ok_iff.mpr ⟨packet.data.sources, packet.source_read, md.current_at⟩
  have hSourceCell : (Frame.ofMountain p.reduced).cell source = md.current :=
    Except.ok.inj ((Canonical.cellAt_of_frame_node p.reduced source).symm.trans hSourceRead)
  have hSourceAt : packet.data.sources[source.2.val]? =
      some ((Frame.ofMountain p.reduced).cell source) := by
    rw [hSourceCell]
    exact md.current_at
  obtain ⟨hNoPremature, hPP, hPL⟩ :=
    packet.state.column_data_parent_inputs hLast packet.source_bound packet.data
  obtain ⟨read⟩ := packet.data.effective_copy_read hPP hPL hNoPremature packet.copy_run hSourceAt
  let copy : EffectiveCopyOccurrence p packet.block packet.start packet.references source result := {
    before := packet.before
    column := packet.column
    state := packet.state
    data := packet.data
    read := read
    preserved := packet.preserved }
  have hSourceRow : (Frame.ofMountain result).height node =
      (Frame.ofMountain p.reduced).height source :=
    hRow.trans (congrArg Cell.row hSourceCell).symm
  let physical : PhysicalMarkerRead copy := {
    index := node.2.val
    cell := (Frame.ofMountain result).cell node
    output_at := packet.node_read
    source_row := hSourceRow }
  let execution : ExecutedNodeCopy packet := ⟨source, rfl, copy, rfl, rfl⟩
  have hSourceReal : Real source := by
    by_contra hn
    have hIndex : source.2.val = 0 := by change ¬ 0 < source.2.val at hn; omega
    have hPhantom : (Frame.ofMountain p.reduced).cell source = phantom := by
      change (Frame.ofMountain p.reduced).cells source.1 source.2 = phantom
      have he : source.2 = ⟨0, hIndex ▸ source.2.isLt⟩ := Fin.ext hIndex
      rw [he]
      exact (build_normal_of_success p.reduced_build).toOrdered.phantom _ _
    have hPositive := Frame.one_le_height hValid.toOrdered hReal
    rw [hSourceRow, Frame.height, hPhantom] at hPositive
    exact (not_le_of_gt Row.zero_lt_one) hPositive
  have hMarkerRef : Frame.ref source = marker :=
    congrArg₂ Ref.mk (packet.data.marker_columns marker hm).symm rfl
  refine ⟨packet, execution, physical,
    hSourceReal, ?_, ?_⟩
  · change Frame.ref source ∈ packet.data.bucket
    simpa only [hMarkerRef] using hm
  · change (⟨node.1.val, node.2.val⟩ : Ref) = ⟨packet.before.size, node.2.val⟩
    exact congrArg (fun c => Ref.mk c node.2.val) packet.target_column.symm

/-- A real final copied node is already recognized, or is one of the two
actual remaining source classes. All reference-gap endpoints are handled
inside the first alternative, with no induction hypothesis. -/
theorem Preparation.copied_node_recognition_cases
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {node : (Frame.ofMountain result).Node}
    (hColumn : p.reduced.size ≤ node.1.val) (hReal : Real node) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node ∨
      NonmarkerCopyAt p result node ∨ PhysicalMarkerAt p result node := by
  obtain ⟨packet⟩ := p.copied_node_origin hLast hCopies hRun hColumn
  cases packet.origin with
  | effective sourceIndex sourceCell read hIndex _ hUnmarked =>
      obtain ⟨execution, hSourceIndex, hRef⟩ := packet.effective_execution read hIndex
      refine Or.inr (Or.inl ⟨packet, execution, ?_, hRef⟩)
      intro hMarked
      apply hUnmarked
      have hm : Frame.ref execution.source ∈ packet.data.bucket := by
        simpa only [BucketMem, execution.source_column] using hMarked
      have hi : (Frame.ref execution.source).index ∈ packet.data.bucket.map Ref.index :=
        List.mem_map.mpr ⟨Frame.ref execution.source, hm, rfl⟩
      simpa only [Frame.ref, hSourceIndex] using hi
  | physicalMarker marker hm copied _ hCopyRow hShape =>
      exact Or.inr (Or.inr (packet.physical_occurrence hLast
        (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun)
        hReal hm (hShape.1.symm.trans hCopyRow)))
  | referenceGap marker hm gap original hFill hMember hShape _ _ =>
      exact Or.inl (packet.reference_gap_rawParent_eq_P hLast hRun hm hFill hMember hShape)

/-- A local handler restricted to a stated actual origin. These two
strict induction premises are the same as in the finite search induction.
This definition is an outstanding obligation, not a proved recognition
claim or an axiom. -/
def Preparation.LowRecognitionOn {front : List Nat} {last : Nat}
    (p : Preparation front last) (result : Mountain)
    (origin : (Frame.ofMountain result).Node → Prop) : Prop :=
  ∀ (current father : (Frame.ofMountain result).Node),
    p.reduced.size ≤ current.1.val → Real current →
    (Frame.ofMountain result).height current < p.lastTop.row → origin current →
    (Frame.ofMountain result).rawParent current = some father →
    (∀ (node parent : (Frame.ofMountain result).Node),
      node.1.val < current.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent) →
    (∀ (node parent : (Frame.ofMountain result).Node), node.1 = current.1 →
      (Frame.ofMountain result).height current < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some parent →
        (Frame.ofMountain result).P node = some parent) →
    (Frame.ofMountain result).P current = some father

theorem Preparation.low_copied_step_of_source_origins
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hEffective : p.LowRecognitionOn result (NonmarkerCopyAt p result))
    (hPhysical : p.LowRecognitionOn result (PhysicalMarkerAt p result)) :
    p.LowCopiedRecognitionStep result := by
  intro current father hColumn hReal hLow hRaw hLeft hHigher
  rcases p.copied_node_recognition_cases hLast hCopies hRun hColumn hReal with
    hKnown | hEffectiveOrigin | hPhysicalOrigin
  · exact hKnown.symm.trans hRaw
  · exact hEffective current father hColumn hReal hLow hEffectiveOrigin hRaw hLeft hHigher
  · exact hPhysical current father hColumn hReal hLow hPhysicalOrigin hRaw hLeft hHigher

/-- The final search theorem now has no reference-gap obligation. Both
remaining numerical source handlers are still explicit. -/
theorem Preparation.rawParentSearch_of_low_source_origins
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} (hCopies : 0 < copies) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hEffective : p.LowRecognitionOn result (NonmarkerCopyAt p result))
    (hPhysical : p.LowRecognitionOn result (PhysicalMarkerAt p result)) :
    (Frame.ofMountain result).RawParentSearch :=
  p.rawParentSearch_of_low_copied_step hLast hCopies hRun
    (p.low_copied_step_of_source_origins hLast hCopies hRun hEffective hPhysical)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.CopiedNodeOrigin.physical_occurrence
#print axioms OmegaY.Expansion.CopiedNodeOrigin.effective_execution
#print axioms OmegaY.Expansion.Preparation.copied_node_recognition_cases
#print axioms OmegaY.Expansion.Preparation.low_copied_step_of_source_origins
#print axioms OmegaY.Expansion.Preparation.rawParentSearch_of_low_source_origins
