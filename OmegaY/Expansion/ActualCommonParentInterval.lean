/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCommonParentInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAllUpperLift
import OmegaY.Expansion.ActualMarkerBandEvents
import OmegaY.Expansion.ActualCommonParentDepth
import OmegaY.Expansion.ActualNonmarkerSplitEvent

/-!
# Complete common-parent intervals between actual copied upper events

The stable portion ends at the physical next marker, when there is one.
The actual shared fill then covers every event up to its effective target.
The endpoint is handled by the new source parents. All intervals below
refer to real output rows, reads, and events; target normality is unused.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

include copy in
/-- A source marker really has a numerical parent in the original normal
frame, because its recorded upper is an actual source upper. -/
theorem source_parent_some_of_marked (hReal : Real source)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source)) :
    ∃ parent, (Frame.ofMountain p.reduced).P source = some parent := by
  let md := copy.data.marker_data (Frame.ref source) hMarked
  have hColumn : p.reduced[source.1.val]? = some copy.data.sources :=
    (copy.state.base_ambient _ source.1.isLt).symm.trans copy.data.source_column
  have hRead : Canonical.cellAt p.reduced ⟨source.1.val, source.2.val + 1⟩ = .ok md.upper :=
    cellAt_ok_iff.mpr ⟨copy.data.sources, hColumn, md.upper_at⟩
  obtain ⟨upper, hRef, _⟩ := Canonical.frame_node_of_cellAt hRead
  have hUpper := Frame.upper_of_refs (rfl : Frame.ref source = ⟨source.1.val, source.2.val⟩) hRef
  obtain ⟨parent, hParent, _⟩ := (build_normal_of_success p.reduced_build).upper_step source upper hReal hUpper
  exact ⟨parent, hParent⟩

/-- Read a genuine output frontier anywhere below its actual upper.
No copied numerical-parent identification is involved. -/
theorem frontierAt_of_upper_read (hValid : MountainValid result)
    {cut : Row} (hCut : (1 : Row) ≤ cut) {upperCell : Cell}
    (hRead : Canonical.cellAt result ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ = .ok upperCell)
    (hLow : copy.read.outputCell.row ≤ cut) (hHigh : cut < upperCell.row) :
    ∃ node : (Frame.ofMountain result).Node, Frame.ref node = copy.outputRef ∧
      frontierAt hValid.toOrdered cut hCut node.1 = node := by
  obtain ⟨node, hRef, hCell⟩ := Canonical.frame_node_of_cellAt copy.output_read
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hRead
  have hUpper := Frame.upper_of_refs hRef hUpperRef
  refine ⟨node, hRef, frontierAt_eq_of_upper_barrier hValid.toOrdered hCut ?_ ?_⟩
  · exact (congrArg Cell.row hCell).le.trans hLow
  · intro other hOther
    obtain rfl := Option.some.inj (hOther.symm.trans hUpper)
    exact hHigh.trans_eq (congrArg Cell.row hUpperCell).symm

theorem frontierAt_at_output_row (hValid : MountainValid result)
    {cut : Row} (hCut : (1 : Row) ≤ cut) (hRow : copy.read.outputCell.row = cut) :
    ∃ node : (Frame.ofMountain result).Node, Frame.ref node = copy.outputRef ∧
      frontierAt hValid.toOrdered cut hCut node.1 = node := by
  obtain ⟨node, hRef, hCell⟩ := Canonical.frame_node_of_cellAt copy.output_read
  exact ⟨node, hRef, frontierAt_of_height_eq hValid.toOrdered hCut
    ((congrArg Cell.row hCell).trans hRow)⟩

end EffectiveCopyOccurrence

section Actual

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block copies next : Nat} {start ambient : Mountain} {references : List Ref}
  (s : DynamicBlockState p block start references next ambient)
  (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
  (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
    let next ← copyBlock mountain p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)) : Result Mountain) = .ok start)

include s history hLast hStartRun

/-- The source cut is converted to its actual floor event internally.
Only the output frontier witnesses, whose construction is separate, are
accepted by this small conversion lemma. -/
theorem DynamicBlockState.copied_depth_eq_at_frontiers_of_source_cut
    {u z : (Frame.ofMountain p.reduced).Node}
    (hUBefore : u.1.val < next) (hZBefore : z.1.val < next)
    (uCopy : EffectiveCopyOccurrence p block start references u ambient)
    (zCopy : EffectiveCopyOccurrence p block start references z ambient)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {sourceCut : Row} (hCut : (1 : Row) ≤ sourceCut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered sourceCut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered sourceCut hCut z.1 = z)
    (hCommon : (Frame.ofMountain p.reduced).P u = (Frame.ofMountain p.reduced).P z)
    {event : Nat}
    (hActualU : ∃ node : (Frame.ofMountain ambient).Node, Frame.ref node = uCopy.outputRef ∧
      eventFrontier s.ambient_valid.toOrdered event node.1 = node)
    (hActualZ : ∃ node : (Frame.ofMountain ambient).Node, Frame.ref node = zCopy.outputRef ∧
      eventFrontier s.ambient_valid.toOrdered event node.1 = node) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      uCopy.outputRef.column =
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      zCopy.outputRef.column := by
  obtain ⟨sourceEvent, hEvent, _, _, hAll⟩ := event_floor_at_cut
    (build_normal_of_success p.reduced_build).toOrdered hCut
  obtain ⟨actualU, hURef, hUF⟩ := hActualU
  obtain ⟨actualZ, hZRef, hZF⟩ := hActualZ
  have hEq := s.depth_eq_of_source_parent_eq history hLast hStartRun hUBefore hZBefore
    uCopy zCopy hURef hZRef hSourceWidth hTargetWidth hEvent
    ((hAll _).trans hUFront) ((hAll _).trans hZFront) hUF hZF hCommon
  simpa only [show actualU.1.val = uCopy.outputRef.column from congrArg Ref.column hURef,
    show actualZ.1.val = zCopy.outputRef.column from congrArg Ref.column hZRef] using hEq

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.source_parent_some_of_marked
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.frontierAt_of_upper_read
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.frontierAt_at_output_row
#print axioms OmegaY.Expansion.DynamicBlockState.copied_depth_eq_at_frontiers_of_source_cut
