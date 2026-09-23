/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowFrontierCopy.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighFrontierCopy

/-!
# Actual frontiers under each column's own contour lift

For any unmarked source frontier, its effective occurrence is the actual
frontier at the lifted source cut. The controlling root and target come
from its real copy record. The real immediate upper is recovered from
execution, including the case in which the source upper is a marker.

There is no cap restriction: the exact lift is strictly increasing above
its root, including when a source upper crosses the cap and resets. No
source numerical-parent condition is needed for this single-column fact.
Different source columns may still use different lifts; a common event
sampling does not follow from this theorem alone.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- The cut map belonging to this occurrence's actual controlling marker. -/
def contourCut (cut : Row) : Row :=
  Row.lift (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row
    (copy.data.marker_data copy.read.marker copy.read.marker_mem).targetCell.row cut

/-- Its domain condition comes from the source read, rather than a chosen
root-interval or an assumed copied-frontier identity. -/
theorem contourCut_one_le {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hBelow : (Frame.ofMountain p.reduced).height source ≤ cut) :
    (1 : Row) ≤ copy.contourCut cut :=
  hCut.trans (Row.lift_ge_source
    (copy.data.marker_data copy.read.marker copy.read.marker_mem).target_lower
    (copy.read.source_lower.trans hBelow))

/-- The exact single-column correspondence at arbitrary cuts. The source
barrier is an original-graph fact; every target read and the target upper
barrier are proved from the actual copying record. -/
theorem frontierAt_own_lift_of_bounds (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hBelow : (Frame.ofMountain p.reduced).height source ≤ cut)
    (hBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper source = some upper →
      cut < (Frame.ofMountain p.reduced).height upper) :
    ∃ node : (Frame.ofMountain result).Node,
      Frame.ref node = copy.outputRef ∧ (Frame.ofMountain result).cell node = copy.read.outputCell ∧
      frontierAt hValid.toOrdered (copy.contourCut cut) (copy.contourCut_one_le hCut hBelow)
        node.1 = node := by
  obtain ⟨node, hRef, hCell⟩ := Canonical.frame_node_of_cellAt copy.output_read
  refine ⟨node, hRef, hCell, ?_⟩
  apply frontierAt_eq_of_upper_barrier hValid.toOrdered (copy.contourCut_one_le hCut hBelow)
  · change ((Frame.ofMountain result).cell node).row ≤ _
    rw [hCell, copy.read.output_row]
    exact Row.lift_monotone copy.read.source_lower hBelow
  · intro upper hUpper
    cases hSourceUpper : (Frame.ofMountain p.reduced).upper source with
    | none =>
        rw [copy.top_upper_none hLast hSourceUpper hRef] at hUpper
        cases hUpper
    | some sourceUpper =>
        obtain ⟨actualUpper, hActualRead, hActualRow⟩ := copy.upper_lift_read hLast hUnmarked hSourceUpper
        have hUpperRef : Frame.ref upper = ⟨copy.outputRef.column, copy.outputRef.index + 1⟩ := by
          have hNodeUpper : Frame.ref upper = ⟨(Frame.ref node).column, (Frame.ref node).index + 1⟩ := by
            simp only [Frame.ref, Ref.mk.injEq]
            exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
          simpa only [hRef] using hNodeUpper
        have hActualCell : (Frame.ofMountain result).cell upper = actualUpper := Except.ok.inj
          ((Canonical.cellAt_of_frame_node result upper).symm.trans (by simpa only [hUpperRef] using hActualRead))
        change copy.contourCut cut < ((Frame.ofMountain result).cell upper).row
        rw [hActualCell, hActualRow]
        exact Row.lift_strictMono (copy.read.source_lower.trans hBelow) (hBarrier sourceUpper hSourceUpper)

/-- A genuine source frontier supplies all the source bounds internally.
The lifted cut's admissibility is also returned, not assumed. -/
theorem frontierAt_own_lift (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hSourceFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut source.1 = source) :
    ∃ (hLiftCut : (1 : Row) ≤ copy.contourCut cut) (node : (Frame.ofMountain result).Node),
      Frame.ref node = copy.outputRef ∧ (Frame.ofMountain result).cell node = copy.read.outputCell ∧
      frontierAt hValid.toOrdered (copy.contourCut cut) hLiftCut node.1 = node := by
  have hSpec := frontierAt_spec (build_normal_of_success p.reduced_build).toOrdered hCut source.1
  have hBelow : (Frame.ofMountain p.reduced).height source ≤ cut := hSourceFront ▸ hSpec.2.2.1
  exact ⟨copy.contourCut_one_le hCut hBelow,
    copy.frontierAt_own_lift_of_bounds hLast hValid hUnmarked hCut hBelow
      (by simpa only [hSourceFront] using hSpec.2.2.2.2)⟩

/-- The same correspondence for an actual source event, without assuming
that the lifted cut is itself an event in the result. -/
theorem eventFrontier_own_lift (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {event : Nat}
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered event source.1 = source) :
    ∃ (hLiftCut : (1 : Row) ≤ copy.contourCut ((Frame.ofMountain p.reduced).eventCut event))
      (node : (Frame.ofMountain result).Node),
      Frame.ref node = copy.outputRef ∧ (Frame.ofMountain result).cell node = copy.read.outputCell ∧
      frontierAt hValid.toOrdered (copy.contourCut ((Frame.ofMountain p.reduced).eventCut event))
        hLiftCut node.1 = node :=
  copy.frontierAt_own_lift hLast hValid hUnmarked ((Frame.ofMountain p.reduced).eventCut_one_le event) hSourceFront

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.contourCut_one_le
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.frontierAt_own_lift_of_bounds
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.frontierAt_own_lift
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.eventFrontier_own_lift
