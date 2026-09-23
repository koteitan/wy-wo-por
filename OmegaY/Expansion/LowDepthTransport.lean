/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/LowDepthTransport.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowCopiedDepth
import OmegaY.Expansion.RawCommonFrontierDepth

/-!
# Transport of actual lifted-frontier depth certificates

The actual history supplies raw ancestor closure. Hence a certificate's
depth formula holds at any event containing its same copied frontier, not
only the floor event used to construct it. Complete-column preservation
also transports the certificate to a new actual floor event in an extension
or a retained prefix. These are transport lemmas; they do not posit a
shared low-event sampling or numerical normality of an output mountain.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

namespace LowCopiedDepth

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block next : Nat} {start ambient : Mountain} {references : List Ref}
  {s : DynamicBlockState p block start references next ambient}
  {source : (Frame.ofMountain p.reduced).Node} {sourceEvent : Nat}
  {copy : EffectiveCopyOccurrence p block start references source ambient}
  (packet : LowCopiedDepth s source sourceEvent copy)

/-- Event numbers and cuts may differ; the actual starting frontier and
raw ancestor closure determine the same complete depth. -/
theorem at_frontier {copies : Nat}
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {targetEvent : Nat}
    (hFrontier : eventFrontier s.ambient_valid.toOrdered targetEvent packet.targetNode.1 = packet.targetNode) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered packet.target_width
        (ambient.size - 1) targetEvent) packet.targetNode.1.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered packet.source_width
        (p.reduced.size - 1) sourceEvent) source.1.val + packet.increment := by
  obtain ⟨hRaw, hFather⟩ := s.raw_invariants_of_start_run history hLast hStartRun
  have hBound : ambient.size - 1 < ambient.size := by have := packet.target_width; omega
  have hNodeBound : packet.targetNode.1.val ≤ ambient.size - 1 := by
    have hc : packet.targetNode.1.val < ambient.size := packet.targetNode.1.isLt
    omega
  exact (Frame.raw_event_parentDepth_of_common_frontier s.ambient_valid.toOrdered hRaw hFather
    packet.target_width hBound hNodeBound packet.frontier hFrontier).trans packet.depth_eq

/-- A later mountain that preserves the complete copied column supplies
its own actual floor event, with the same read and the same depth increment.
Its floor row need not equal the earlier floor row. -/
theorem preserved_floor {after : Mountain} (hPreserve : PreservesColumns ambient after)
    (hAfter : MountainValid after) :
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
  have hWidth : 0 < after.size := packet.target_width.trans_le hPreserve.size_le
  obtain ⟨event, hEvent, hBelow, hMax, hFrontiers⟩ :=
    event_floor_at_cut hAfter.toOrdered packet.cut_one
  let node := hPreserve.mapNode packet.targetNode
  have hAt : frontierAt s.ambient_valid.toOrdered
      (copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) packet.cut_one
      packet.targetNode.1 = packet.targetNode :=
    (packet.all_frontiers_at_cut packet.targetNode.1).symm.trans packet.frontier
  have hFrontier : eventFrontier hAfter.toOrdered event node.1 = node := by
    rw [hFrontiers]
    have hMapped := hPreserve.mapNode_frontierAt s.ambient_valid.toOrdered hAfter.toOrdered
      packet.cut_one packet.targetNode.1
    simpa only [hAt] using hMapped
  have hDepth := hPreserve.event_parentDepth_at_common_cut s.ambient_valid.toOrdered hAfter.toOrdered
    packet.target_width hWidth packet.cut_one packet.all_frontiers_at_cut hFrontiers packet.targetNode.1.isLt
  refine ⟨hWidth, event, node, hEvent, hBelow, hMax,
    (hPreserve.mapNode_ref packet.targetNode).trans packet.reference,
    (hPreserve.mapNode_cell packet.targetNode).trans packet.cell, hFrontier, ?_⟩
  change parentDepth _ (hPreserve.mapNode packet.targetNode).1.val = _
  rw [hPreserve.mapNode_column]
  exact hDepth.trans packet.depth_eq

/-- Removing later columns keeps the same correction on every surviving
copied node. The explicit survival bound excludes the deleted column and
prevents the event map's out-of-range default from entering the statement. -/
theorem retained_floor {after : Mountain} (hPreserve : PreservesColumns after ambient)
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
  have hRead : cellAt after copy.outputRef = .ok copy.read.outputCell :=
    (hPreserve.cellAt hSurvives).symm.trans copy.output_read
  obtain ⟨node, hRef, hCell⟩ := Canonical.frame_node_of_cellAt hRead
  have hWidth : 0 < after.size := (Nat.zero_le node.1.val).trans_lt node.1.isLt
  have hMapped : hPreserve.mapNode node = packet.targetNode :=
    Executable.ref_injective _ ((hPreserve.mapNode_ref node).trans (hRef.trans packet.reference.symm))
  obtain ⟨event, hEvent, hBelow, hMax, hFrontiers⟩ :=
    event_floor_at_cut hAfter.toOrdered packet.cut_one
  have hAt : frontierAt s.ambient_valid.toOrdered
      (copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) packet.cut_one
      packet.targetNode.1 = packet.targetNode :=
    (packet.all_frontiers_at_cut packet.targetNode.1).symm.trans packet.frontier
  have hFrontier : eventFrontier hAfter.toOrdered event node.1 = node := by
    rw [hFrontiers]
    let chosen := frontierAt hAfter.toOrdered
      (copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) packet.cut_one node.1
    have hChosen := hPreserve.mapNode_frontierAt hAfter.toOrdered s.ambient_valid.toOrdered
      packet.cut_one node.1
    have hCol : (hPreserve.mapNode chosen).1 = packet.targetNode.1 := by
      apply Fin.ext
      rw [hPreserve.mapNode_column]
      have hNodeCol := congrArg (fun n => n.1.val) hMapped
      rw [hPreserve.mapNode_column] at hNodeCol
      exact hNodeCol
    change frontierAt s.ambient_valid.toOrdered _ packet.cut_one
      (hPreserve.mapNode chosen).1 = hPreserve.mapNode chosen at hChosen
    rw [hCol, hAt] at hChosen
    apply Executable.ref_injective (Frame.ofMountain after)
    exact (hPreserve.mapNode_ref chosen).symm.trans
      ((congrArg Frame.ref (hChosen.symm.trans hMapped.symm)).trans (hPreserve.mapNode_ref node))
  have hDepth := hPreserve.event_parentDepth_at_common_cut hAfter.toOrdered s.ambient_valid.toOrdered
    hWidth packet.target_width packet.cut_one hFrontiers packet.all_frontiers_at_cut node.1.isLt
  have hColumn : node.1.val = packet.targetNode.1.val :=
    (hPreserve.mapNode_column node).symm.trans (congrArg (fun n => n.1.val) hMapped)
  refine ⟨hWidth, event, node, hEvent, hBelow, hMax, hRef, hCell, hFrontier, ?_⟩
  exact hDepth.symm.trans (by simpa only [hColumn] using packet.depth_eq)

end LowCopiedDepth
end OmegaY.Expansion

#print axioms OmegaY.Expansion.LowCopiedDepth.at_frontier
#print axioms OmegaY.Expansion.LowCopiedDepth.preserved_floor
#print axioms OmegaY.Expansion.LowCopiedDepth.retained_floor
