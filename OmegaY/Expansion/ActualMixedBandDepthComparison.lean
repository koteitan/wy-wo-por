/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMixedBandDepthComparison.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMixedSourceDepthOrder
import OmegaY.Expansion.ActualMarkerBandPathDepth
import OmegaY.Expansion.RecognizedRootBandDepth

/-!
# No reversed depth comparison within a mixed marker band

Numerical recognition is used only for the complete block-start prefix,
which is strictly earlier than every copied column considered here. It
allows its endpoint boundary-depth bound to be projected to earlier cuts.
The actual single-band path balance then bounds every marked-column event
depth from below by its source depth. The mixed unmarked column has its
original depth at every cut, and source geometry forces that depth lower.

No recognition of the current copied column or its inserted nodes is input.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)
  (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
  (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
    node.1.val < start.size → Real node →
    (Frame.ofMountain ambient).rawParent node = some parent →
      (Frame.ofMountain ambient).P node = some parent)

include s history hLast hStartRun hSourceWidth hTargetWidth hKnown

/-- A genuine marked column has at least its source event depth throughout
the closed physical/effective band. The endpoint uses its already proved
actual frontier correction; interior events use actual filled parent paths. -/
theorem DynamicBlockState.marked_band_depth_le_of_left_recognition
    {source : (Frame.ofMountain p.reduced).Node}
    (hBefore : source.1.val < next)
    (copy : EffectiveCopyOccurrence p block start references source ambient)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {sourceEvent targetEvent : Nat} (hEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hSource : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent source.1 = source)
    (hLow : (Frame.ofMountain p.reduced).eventCut sourceEvent ≤ (Frame.ofMountain ambient).eventCut targetEvent)
    (hHigh : (Frame.ofMountain ambient).eventCut targetEvent ≤ copy.read.outputCell.row) :
    parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
      hSourceWidth (p.reduced.size - 1) sourceEvent) source.1.val ≤
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth
        (ambient.size - 1) targetEvent) copy.outputRef.column := by
  have hNormal := build_normal_of_success p.reduced_build
  have hReal : Real source := hSource ▸ (eventFrontier_spec hNormal.toOrdered sourceEvent source.1).2.1
  obtain ⟨index, a⟩ := copy.state.actual_marker_root_interval hLast hMarked
    (Canonical.cellAt_of_frame_node p.reduced source)
    (Row.zero_lt_one.trans_le (one_le_height hNormal.toOrdered hReal))
  obtain ⟨a⟩ := a
  obtain ⟨low, _, hLowColumn, hLowRow, path⟩ := a.rootCone_of_marker hMarked rfl
  have hLowEq : low = source := node_eq_of_column_height hNormal.toOrdered hLowColumn
    (hLowRow.trans a.root_row)
  subst low
  have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
  have hRootIndex : a.root.2.val = index := congrArg Ref.index a.root_ref
  have hRow := copy.marked_frontier_cut_eq hMarked
    ((Frame.ofMountain p.reduced).eventCut_one_le sourceEvent) hSource
  have hOwnCut : copy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent) =
      copy.read.outputCell.row := by rw [hRow]; exact copy.read.output_row.symm
  obtain ⟨lastBad, _, _, ⟨packet⟩⟩ := s.actual_all_source_root_path_depth_of_path history hLast hStartRun
    path hRootColumn copy.state.next_lower hBefore copy hEvent hSource
  rcases lt_or_eq_of_le hHigh with hInterior | hEndpoint
  · have hQuery : referenceAt start references ((Frame.ofMountain p.reduced).height a.root) =
        .ok copy.read.outputCell.row := by
      rw [a.root_row]
      exact (copy.state.referenceAt_preserved _).symm.trans (copy.read.marked_reference hMarked)
    have hBalance := s.marker_band_path_depth_balance history hLast hSourceWidth hTargetWidth path
      a.root_real hRootColumn (by rw [hRootIndex]; exact a.root_prefix) a.root_row.symm hBefore hSource hQuery
      (by rw [a.root_row]; change (Frame.ofMountain p.reduced).height source ≤ _
          rw [← hRow]; exact hLow) hInterior
    have hBoundary := packet.boundary_depth_le_at_earlier_cut_of_left_recognition hLast hStartRun hKnown
      (hHigh.trans_eq hOwnCut.symm)
    change parentDepth (eventParentMap hNormal.toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) a.root.1.val ≤
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth
        (ambient.size - 1) targetEvent) (start.size - 1) at hBoundary
    dsimp only at hBalance
    rw [hRootColumn, s.boundary_copy_index] at hBalance
    rw [hRootColumn] at hBoundary
    rw [copy.source_column]
    omega
  · obtain ⟨increment, _, hDepth⟩ := packet.correction hLast hStartRun
    let certified := packet.copied.toCorrected increment hDepth
    have hAtOwn := (packet.copied.all_frontiers_at_cut packet.copied.childNode.1).symm.trans
      packet.copied.child_frontier
    have hAtEvent : eventFrontier s.ambient_valid.toOrdered targetEvent certified.targetNode.1 =
        certified.targetNode := by
      change frontierAt s.ambient_valid.toOrdered ((Frame.ofMountain ambient).eventCut targetEvent)
        _ packet.copied.childNode.1 = packet.copied.childNode
      simpa only [hEndpoint, hOwnCut] using hAtOwn
    have hActual := certified.at_frontier history hLast hStartRun hAtEvent
    change parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth
        (ambient.size - 1) targetEvent) packet.copied.childNode.1.val =
      parentDepth (eventParentMap hNormal.toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) source.1.val + increment at hActual
    have hColumn : packet.copied.childNode.1.val = copy.outputRef.column :=
      congrArg Ref.column packet.copied.child_reference
    rw [hColumn] at hActual
    omega

/-- The mixed pair is strictly ordered at every event in the whole closed
band, including unrelated-column events and the effective endpoint. -/
theorem DynamicBlockState.mixed_band_depth_lt_of_left_recognition
    {marked other candidate : (Frame.ofMountain p.reduced).Node}
    (hMarkedBefore : marked.1.val < next) (hOtherBefore : other.1.val < next)
    (markedCopy : EffectiveCopyOccurrence p block start references marked ambient)
    (otherCopy : EffectiveCopyOccurrence p block start references other ambient)
    (hMarked : BucketMem p.marked marked.1.val (Frame.ref marked))
    (hUnmarked : other.2.val ∉ (p.marked[other.1.val]?.getD []).map Ref.index)
    (hSameRow : (Frame.ofMountain p.reduced).height marked = (Frame.ofMountain p.reduced).height other)
    (hMarkedQ : (Frame.ofMountain p.reduced).Q marked = some candidate)
    (hOtherQ : (Frame.ofMountain p.reduced).Q other = some candidate)
    {sourceEvent targetEvent : Nat} (hEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hMarkedFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent marked.1 = marked)
    (hOtherFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent other.1 = other)
    (hLow : (Frame.ofMountain p.reduced).eventCut sourceEvent ≤ (Frame.ofMountain ambient).eventCut targetEvent)
    (hHigh : (Frame.ofMountain ambient).eventCut targetEvent ≤ markedCopy.read.outputCell.row) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
      otherCopy.outputRef.column <
      parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) targetEvent)
        markedCopy.outputRef.column := by
  have hNormal := build_normal_of_success p.reduced_build
  have hFixed := s.mixed_band_unmarked_depth_eq history hLast hStartRun hSourceWidth hTargetWidth
    hOtherBefore markedCopy otherCopy hMarked hUnmarked hSameRow hMarkedQ hOtherQ
    hEvent hMarkedFront hOtherFront hLow hHigh
  have hIncreased := s.marked_band_depth_le_of_left_recognition history hLast hStartRun
    hSourceWidth hTargetWidth hKnown hMarkedBefore markedCopy hMarked hEvent hMarkedFront hLow hHigh
  have hReal : Real marked := hMarkedFront ▸ (eventFrontier_spec hNormal.toOrdered sourceEvent marked.1).2.1
  obtain ⟨index, a⟩ := markedCopy.state.actual_marker_root_interval hLast hMarked
    (Canonical.cellAt_of_frame_node p.reduced marked)
    (Row.zero_lt_one.trans_le (one_le_height hNormal.toOrdered hReal))
  obtain ⟨a⟩ := a
  have hNotMarked : ¬ BucketMem p.marked other.1.val (Frame.ref other) := by
    intro hm
    exact hUnmarked (List.mem_map.mpr ⟨Frame.ref other, hm, rfl⟩)
  have hSourceOrder := a.mixed_source_event_depth_lt hSourceWidth hMarked hNotMarked
    markedCopy.state.next_lower otherCopy.state.next_lower rfl hSameRow.symm hMarkedQ hOtherQ
    hMarkedFront hOtherFront
  exact hFixed.trans_lt (hSourceOrder.trans_le hIncreased)

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.marked_band_depth_le_of_left_recognition
#print axioms OmegaY.Expansion.DynamicBlockState.mixed_band_depth_lt_of_left_recognition
