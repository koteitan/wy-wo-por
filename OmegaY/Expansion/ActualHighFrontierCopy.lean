/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighFrontierCopy.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualNextHighestBoundary
import OmegaY.Expansion.ActualLowEffectiveCandidate

/-!
# Actual effective source frontiers at every high cut

A source frontier at a cut at least Z cannot be a marker: a marker has
its immediate successor at or below its actual cap, which is at most Z.
The copied lower remains below the cut, while its upper above the cut has
unchanged height. Source tops are actual copied tops. This identifies the
true target frontier without assuming copied normality or parent search.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

include copy in
theorem unmarked_of_high_upper_barrier (hLast : 1 < last)
    (hReal : Real source) {cut : Row} (hHigh : p.lastTop.row ≤ cut)
    (hBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper source = some upper →
      cut < (Frame.ofMountain p.reduced).height upper) :
    source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index := by
  intro hMarked
  obtain ⟨marker, hm, hIndex⟩ := List.mem_map.mp hMarked
  have hSourceColumn : p.reduced[source.1.val]? = some copy.data.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans copy.data.source_column
  obtain ⟨hSuccessor, _⟩ := copy.data.prepared_real_marker_successor hSourceColumn hm
    (by simpa only [hIndex, Frame.Real] using hReal)
  obtain ⟨degree, _, hCap⟩ := copy.state.marker_caps_below_lastTop hLast copy.data source.1.isLt marker hm
  have hUpperRead : Canonical.cellAt p.reduced ⟨source.1.val, source.2.val + 1⟩ =
      .ok (copy.data.marker_data marker hm).upper := cellAt_ok_iff.mpr
    ⟨copy.data.sources, hSourceColumn, by simpa only [hIndex] using (copy.data.marker_data marker hm).upper_at⟩
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hUpper : (Frame.ofMountain p.reduced).upper source = some upper :=
    Frame.upper_of_refs rfl hUpperRef
  have hBound : (Frame.ofMountain p.reduced).height upper ≤ p.lastTop.row := by
    change ((Frame.ofMountain p.reduced).cell upper).row ≤ _
    rw [hUpperCell, hSuccessor]
    exact (Row.bump_mono_exponent _ (Nat.zero_le degree)).trans hCap
  exact not_lt_of_ge (hBound.trans hHigh) (hBarrier upper hUpper)

theorem frontierAt_high_of_bounds (hLast : 1 < last) (hValid : MountainValid result)
    {cut : Row} (hCut : (1 : Row) ≤ cut) (hHigh : p.lastTop.row ≤ cut)
    (hReal : Real source) (hBelow : (Frame.ofMountain p.reduced).height source ≤ cut)
    (hBarrier : ∀ upper, (Frame.ofMountain p.reduced).upper source = some upper →
      cut < (Frame.ofMountain p.reduced).height upper) :
    ∃ node : (Frame.ofMountain result).Node,
      Frame.ref node = copy.outputRef ∧ (Frame.ofMountain result).cell node = copy.read.outputCell ∧
      frontierAt hValid.toOrdered cut hCut node.1 = node := by
  let F := Frame.ofMountain p.reduced
  have hUnmarked := copy.unmarked_of_high_upper_barrier hLast hReal hHigh hBarrier
  obtain ⟨node, hRef, hCell⟩ := Canonical.frame_node_of_cellAt copy.output_read
  refine ⟨node, hRef, hCell, ?_⟩
  apply frontierAt_eq_of_upper_barrier hValid.toOrdered hCut
  · change ((Frame.ofMountain result).cell node).row ≤ _
    rw [hCell]
    by_cases hSourceHigh : p.lastTop.row ≤ F.height source
    · rw [copy.high_row hLast hSourceHigh]
      exact hBelow
    · exact (copy.row_lt_lastTop hLast (lt_of_not_ge hSourceHigh)).le.trans hHigh
  · intro upper hUpper
    cases hSourceUpper : F.upper source with
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
        obtain ⟨degree, hTarget, hCap⟩ := copy.state.marker_caps_below_lastTop
          hLast copy.data source.1.isLt copy.read.marker copy.read.marker_mem
        have hSourceAbove := hBarrier sourceUpper hSourceUpper
        have hFixed := Row.lift_eq_of_ge_cap
          (copy.data.marker_data copy.read.marker copy.read.marker_mem).target_lower hTarget
          (hCap.trans (hHigh.trans hSourceAbove.le))
        change cut < ((Frame.ofMountain result).cell upper).row
        rw [hActualCell, hActualRow, hFixed]
        exact hSourceAbove

theorem frontierAt_high (hLast : 1 < last) (hValid : MountainValid result)
    {event : Nat}
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut event)
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered event source.1 = source) :
    ∃ node : (Frame.ofMountain result).Node,
      Frame.ref node = copy.outputRef ∧ (Frame.ofMountain result).cell node = copy.read.outputCell ∧
      frontierAt hValid.toOrdered ((Frame.ofMountain p.reduced).eventCut event)
        ((Frame.ofMountain p.reduced).eventCut_one_le event) node.1 = node := by
  have hSpec := eventFrontier_spec (build_normal_of_success p.reduced_build).toOrdered event source.1
  exact copy.frontierAt_high_of_bounds hLast hValid ((Frame.ofMountain p.reduced).eventCut_one_le event)
    hHigh (hSourceFront ▸ hSpec.2.1) (hSourceFront ▸ hSpec.2.2.1)
    (by simpa only [hSourceFront] using hSpec.2.2.2.2)

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.unmarked_of_high_upper_barrier
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.frontierAt_high_of_bounds
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.frontierAt_high
