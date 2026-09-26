/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FinalLiftedDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAllSourceDepth
import OmegaY.Expansion.LowDepthTransport
import OmegaY.Expansion.ExecutedBlockPrefix
import OmegaY.Expansion.FinalHighEventSampling

/-!
# Actual lifted-frontier depths in the returned expansion

Any positive executed block can be recovered with its actual history.
The all-source depth certificate at that block's own contour cut survives
later blocks and the final pop. A retained column is required explicitly.

The result keeps its executed block, effective source occurrence and exact
lifted cut. It is not an arbitrary existential depth bound. Different
columns can still choose different cuts; no comparison between their words
or expansion well-foundedness is asserted here.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem LowCopiedDepth.common_prefix_floor
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    {s : DynamicBlockState p block start references next ambient}
    {source : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
    {copy : EffectiveCopyOccurrence p block start references source ambient}
    (packet : LowCopiedDepth s source sourceEvent copy)
    {common after : Mountain} (hAmbient : PreservesColumns ambient common)
    (hAfterPrefix : PreservesColumns after common)
    (hAfter : MountainValid after) (hSurvives : copy.outputRef.column < after.size) :
    ∃ (hWidth : 0 < after.size) (event : Nat) (node : (Frame.ofMountain after).Node),
      event ≤ (Frame.ofMountain after).lastEvent ∧
      (Frame.ofMountain after).eventCut event ≤
        copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) ∧
      (∀ row ∈ (Frame.ofMountain after).eventCuts,
        row ≤ copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) →
          row ≤ (Frame.ofMountain after).eventCut event) ∧
      Frame.ref node = copy.outputRef ∧
      (Frame.ofMountain after).cell node = copy.read.outputCell ∧
      eventFrontier hAfter.toOrdered event node.1 = node ∧
      parentDepth (eventParentMap hAfter.toOrdered hWidth (after.size - 1) event) node.1.val =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered packet.source_width
          (p.reduced.size - 1) sourceEvent) source.1.val + packet.increment := by
  rcases Nat.le_total ambient.size after.size with hSize | hSize
  · exact packet.preserved_floor (hAmbient.between_prefixes hAfterPrefix hSize) hAfter
  · exact packet.retained_floor (hAfterPrefix.between_prefixes hAmbient hSize) hAfter hSurvives

/-- A returned-depth witness retains its actual execution provenance,
including the source-dependent lifted cut and complete output cell. -/
structure ReturnedCopiedDepth {front : List Nat} {last : Nat}
    (p : Preparation front last) (copies block : Nat)
    (source : (Frame.ofMountain p.reduced).Node) (sourceEvent : Nat) (result : Mountain) where
  full : Mountain
  full_run : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok full
  returned : full.pop = result
  executed : ExecutedBlockPrefix p block full
  copy : EffectiveCopyOccurrence p block executed.start executed.references source executed.completed
  localDepth : LowCopiedDepth executed.state source sourceEvent copy
  valid : MountainValid result
  width : 0 < result.size
  targetEvent : Nat
  targetNode : (Frame.ofMountain result).Node
  target_event_end : targetEvent ≤ (Frame.ofMountain result).lastEvent
  target_event_below : (Frame.ofMountain result).eventCut targetEvent ≤
    copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)
  target_event_maximal : ∀ row ∈ (Frame.ofMountain result).eventCuts,
    row ≤ copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) →
      row ≤ (Frame.ofMountain result).eventCut targetEvent
  reference : Frame.ref targetNode = copy.outputRef
  cell : (Frame.ofMountain result).cell targetNode = copy.read.outputCell
  column : targetNode.1.val = source.1.val + block * (p.reduced.size - 1 - p.root.column)
  frontier : eventFrontier valid.toOrdered targetEvent targetNode.1 = targetNode
  depth_eq : parentDepth (eventParentMap valid.toOrdered width (result.size - 1) targetEvent)
        targetNode.1.val =
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered localDepth.source_width
      (p.reduced.size - 1) sourceEvent) source.1.val + localDepth.increment

/-- Every surviving source occurrence in every actual positive block has
its constructed lifted-event depth formula in the final returned mountain.
All source markers and all exits of their parent chains are included. -/
theorem Preparation.expandDiagram_copied_depth
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies block : Nat} {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hPositive : 0 < block) (hBlock : block ≤ copies)
    {source : (Frame.ofMountain p.reduced).Node} (hRight : p.root.column < source.1.val)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered
      sourceEvent source.1 = source)
    (hSurvives : source.1.val + block * (p.reduced.size - 1 - p.root.column) < result.size) :
    Nonempty (ReturnedCopiedDepth p copies block source sourceEvent result) := by
  have hCopies : 0 < copies := hPositive.trans_le hBlock
  obtain ⟨full, hFullRun, ready⟩ := p.blocks_total hLast copies
  have hReturned : full.pop = result := Except.ok.inj
    ((p.expandDiagram_of_blocks hLast hCopies hFullRun).symm.trans hRun)
  have hValid : MountainValid result := hReturned ▸ ready.valid.pop
  have hResultPrefix : PreservesColumns result full := hReturned ▸ PreservesColumns.pop_prefix full
  obtain ⟨executed⟩ := p.blocks_executed_prefix hLast hFullRun hPositive hBlock
  obtain ⟨copy, ⟨localDepth⟩⟩ := executed.state.actual_all_source_copied_depth_exists
    executed.history hLast executed.start_run hRight source.1.isLt hSourceEvent hSourceFront
  have hRefSurvives : copy.outputRef.column < result.size := by
    rw [copy.source_column]
    exact hSurvives
  obtain ⟨hWidth, event, node, hEvent, hBelow, hMax, hRef, hCell, hFrontier, hDepth⟩ :=
    localDepth.common_prefix_floor executed.preserved hResultPrefix hValid hRefSurvives
  exact ⟨{
    full := full
    full_run := hFullRun
    returned := hReturned
    executed := executed
    copy := copy
    localDepth := localDepth
    valid := hValid
    width := hWidth
    targetEvent := event
    targetNode := node
    target_event_end := hEvent
    target_event_below := hBelow
    target_event_maximal := hMax
    reference := hRef
    cell := hCell
    column := (congrArg Ref.column hRef).trans copy.source_column
    frontier := hFrontier
    depth_eq := hDepth }⟩

/-- The real source event enumeration chooses the source frontier too;
the caller specifies only its column, event and surviving copied block. -/
theorem Preparation.expandDiagram_column_lifted_depth
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies block : Nat} {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hPositive : 0 < block) (hBlock : block ≤ copies)
    (sourceColumn : Fin (Frame.ofMountain p.reduced).width)
    (hRight : p.root.column < sourceColumn.val)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSurvives : sourceColumn.val + block * (p.reduced.size - 1 - p.root.column) < result.size) :
    Nonempty (ReturnedCopiedDepth p copies block
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent sourceColumn)
      sourceEvent result) := by
  exact p.expandDiagram_copied_depth hLast hRun hPositive hBlock hRight hSourceEvent rfl hSurvives

end OmegaY.Expansion

#print axioms OmegaY.Expansion.LowCopiedDepth.common_prefix_floor
#print axioms OmegaY.Expansion.Preparation.expandDiagram_copied_depth
#print axioms OmegaY.Expansion.Preparation.expandDiagram_column_lifted_depth
