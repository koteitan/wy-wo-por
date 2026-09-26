/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMarkedFrontierCopy.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowFrontierCopy
import OmegaY.Expansion.ActualPhysicalMarkerSearch

/-!
# Actual physical and effective frontiers of source markers

A real prepared marker has its immediate source successor at row rho+1.
Consequently, an admissible source cut having this marker as frontier is
exactly rho. Its physical occurrence is the target frontier at rho; its
effective occurrence is the target frontier at its real target row,
which is its own contour lift of rho. The latter is an actual event row.

These are single-column assertions at genuine whole-frame cuts/events.
They do not identify different columns' contour lifts or prove a common
sampling of all source frontiers. No copied numerical-parent recognition
is assumed. Both stationary and raised targets are covered.
-/

namespace OmegaY.Geometry.Frame

/-- A stored real row is the actual inclusive frontier of its own column
at precisely that row. -/
theorem frontierAt_own_height {F : Frame} (hF : F.Ordered) {node : F.Node}
    (hOne : (1 : Row) ≤ F.height node) :
    frontierAt hF (F.height node) hOne node.1 = node := by
  apply frontierAt_eq_of_upper_barrier hF hOne le_rfl
  intro upper hUpper
  obtain ⟨hColumn, hIndex⟩ := upper_spec hUpper
  rcases upper with ⟨column, index⟩
  dsimp only at hColumn hIndex
  subst column
  exact hF.rows_strict node.1 (by change node.2.val < index.val; omega)

theorem frontierAt_of_height_eq {F : Frame} (hF : F.Ordered) {node : F.Node}
    {cut : Row} (hCut : (1 : Row) ≤ cut) (hRow : F.height node = cut) :
    frontierAt hF cut hCut node.1 = node := by
  subst cut
  exact frontierAt_own_height hF hCut

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

include copy in
/-- The source cut is derived from the actual marker successor and the
actual frontier maximum. It is not supplied as an extra row hypothesis. -/
theorem marked_frontier_cut_eq
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hSourceFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      cut hCut source.1 = source) :
    cut = (Frame.ofMountain p.reduced).height source := by
  let F := Frame.ofMountain p.reduced
  let md := copy.data.marker_data (Frame.ref source) hMarked
  have hSpec := frontierAt_spec (build_normal_of_success p.reduced_build).toOrdered hCut source.1
  have hReal : Real source := hSourceFront ▸ hSpec.2.1
  have hBelow : F.height source ≤ cut := hSourceFront ▸ hSpec.2.2.1
  have hSourceColumn : p.reduced[source.1.val]? = some copy.data.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans copy.data.source_column
  have hCurrent : md.current = F.cell source :=
    Option.some.inj (md.current_at.symm.trans copy.read.source_at)
  obtain ⟨hSuccessor, _⟩ := copy.data.prepared_real_marker_successor hSourceColumn hMarked hReal
  have hUpperRead : Canonical.cellAt p.reduced ⟨source.1.val, source.2.val + 1⟩ = .ok md.upper :=
    cellAt_ok_iff.mpr ⟨copy.data.sources, hSourceColumn, md.upper_at⟩
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hUpper : F.upper source = some upper := Frame.upper_of_refs rfl hUpperRef
  have hBarrier : cut < F.height upper := by
    have hAll : ∀ next, F.upper source = some next → cut < F.height next := by
      simpa only [hSourceFront] using hSpec.2.2.2.2
    exact hAll upper hUpper
  have hSuccessorRow : F.height upper = Row.bump (F.height source) 0 :=
    (congrArg Cell.row hUpperCell).trans
      (hSuccessor.trans (congrArg (fun cell : Cell => Row.bump cell.row 0) hCurrent))
  rw [hSuccessorRow] at hBarrier
  exact (Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero (Row.jump_le_of_lt_bump hBelow hBarrier))).symm

/-- The actual marked effective occurrence is the frontier at its own
lifted source cut, including genuinely raised targets. No source P is
required, so parents in the root column are covered too. -/
theorem frontierAt_own_lift_of_marked (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hSourceFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      cut hCut source.1 = source) :
    ∃ (hLiftCut : (1 : Row) ≤ copy.contourCut cut) (node : (Frame.ofMountain result).Node),
      Frame.ref node = copy.outputRef ∧ (Frame.ofMountain result).cell node = copy.read.outputCell ∧
      frontierAt hValid.toOrdered (copy.contourCut cut) hLiftCut node.1 = node := by
  have hCutEq := copy.marked_frontier_cut_eq hMarked hCut hSourceFront
  have hBelow : (Frame.ofMountain p.reduced).height source ≤ cut := hCutEq.symm.le
  have hLiftCut := copy.contourCut_one_le hCut hBelow
  obtain ⟨node, hRef, hCell⟩ := Canonical.frame_node_of_cellAt copy.output_read
  have hRow : (Frame.ofMountain result).height node = copy.contourCut cut := by
    change ((Frame.ofMountain result).cell node).row = _
    rw [hCell, copy.read.output_row, hCutEq]
    rfl
  refine ⟨hLiftCut, node, hRef, hCell, ?_⟩
  exact frontierAt_of_height_eq hValid.toOrdered hLiftCut hRow

/-- Complete single-column source-frontier coverage. The executable
marker bucket decides between its successor argument and the actual
nonmarker contour-adjacency argument. -/
theorem frontierAt_own_lift_all (hLast : 1 < last) (hValid : MountainValid result)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hSourceFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      cut hCut source.1 = source) :
    ∃ (hLiftCut : (1 : Row) ≤ copy.contourCut cut) (node : (Frame.ofMountain result).Node),
      Frame.ref node = copy.outputRef ∧ (Frame.ofMountain result).cell node = copy.read.outputCell ∧
      frontierAt hValid.toOrdered (copy.contourCut cut) hLiftCut node.1 = node := by
  by_cases hIndex : source.2.val ∈ (p.marked[source.1.val]?.getD []).map Ref.index
  · obtain ⟨marker, hm, hMarkerIndex⟩ := List.mem_map.mp hIndex
    have hColumn := copy.data.marker_columns marker hm
    have hRef : marker = Frame.ref source := congrArg₂ Ref.mk hColumn hMarkerIndex
    have hMarked : BucketMem p.marked source.1.val (Frame.ref source) := hRef ▸ hm
    exact copy.frontierAt_own_lift_of_marked hValid hMarked hCut hSourceFront
  · exact copy.frontierAt_own_lift hLast hValid hIndex hCut hSourceFront

theorem eventFrontier_own_lift_all (hLast : 1 < last) (hValid : MountainValid result)
    {event : Nat}
    (hSourceFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered event source.1 = source) :
    ∃ (hLiftCut : (1 : Row) ≤ copy.contourCut ((Frame.ofMountain p.reduced).eventCut event))
      (node : (Frame.ofMountain result).Node),
      Frame.ref node = copy.outputRef ∧ (Frame.ofMountain result).cell node = copy.read.outputCell ∧
      frontierAt hValid.toOrdered (copy.contourCut ((Frame.ofMountain p.reduced).eventCut event))
        hLiftCut node.1 = node :=
  copy.frontierAt_own_lift_all hLast hValid ((Frame.ofMountain p.reduced).eventCut_one_le event) hSourceFront

/-- A marker's lifted cut is itself an actual global event row, not
merely a cut whose floor event has the same frontier. Only the copied
source column is identified at this event. -/
theorem actual_event_of_marked_frontier (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hSourceFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      cut hCut source.1 = source) :
    ∃ (event : Nat) (node : (Frame.ofMountain result).Node),
      event ≤ (Frame.ofMountain result).lastEvent ∧
      (Frame.ofMountain result).eventCut event = copy.contourCut cut ∧
      Frame.ref node = copy.outputRef ∧ (Frame.ofMountain result).cell node = copy.read.outputCell ∧
      eventFrontier hValid.toOrdered event node.1 = node := by
  have hCutEq := copy.marked_frontier_cut_eq hMarked hCut hSourceFront
  obtain ⟨hLiftCut, node, hRef, hCell, _⟩ :=
    copy.frontierAt_own_lift_of_marked hValid hMarked hCut hSourceFront
  have hRow : (Frame.ofMountain result).height node = copy.contourCut cut := by
    change ((Frame.ofMountain result).cell node).row = _
    rw [hCell, copy.read.output_row, hCutEq]
    rfl
  obtain ⟨event, hEvent, hEventRow⟩ := eventCut_of_member
    (mem_eventCuts.mpr (height_mem_eventRows node (hRow.symm ▸ hLiftCut)))
  exact ⟨event, node, hEvent, hEventRow.trans hRow, hRef, hCell,
    frontierAt_of_height_eq hValid.toOrdered ((Frame.ofMountain result).eventCut_one_le event) hEventRow.symm⟩

end EffectiveCopyOccurrence

namespace PhysicalMarkerRead

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node}
  {copy : EffectiveCopyOccurrence p block start references source result}
  (physical : PhysicalMarkerRead copy)

/-- Physical markers remain frontiers at the original source cut, even
when their effective endpoints lie strictly above it. This statement uses
only actual reads, source successor geometry and target row ordering. -/
theorem frontierAt_source_cut (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hSourceFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      cut hCut source.1 = source) :
    ∃ node : (Frame.ofMountain result).Node,
      Frame.ref node = physical.outputRef ∧ (Frame.ofMountain result).cell node = physical.cell ∧
      frontierAt hValid.toOrdered cut hCut node.1 = node := by
  have hCutEq := copy.marked_frontier_cut_eq hMarked hCut hSourceFront
  obtain ⟨node, hRef, hCell⟩ := Canonical.frame_node_of_cellAt physical.output_read
  have hRow : (Frame.ofMountain result).height node = cut :=
    (congrArg Cell.row hCell).trans (physical.source_row.trans hCutEq.symm)
  refine ⟨node, hRef, hCell, ?_⟩
  exact frontierAt_of_height_eq hValid.toOrdered hCut hRow

/-- The physical source cut also occurs in the actual target event
enumeration. The resulting event frontier is the physical node, regardless
of whether its effective endpoint was raised. -/
theorem actual_event_at_source_cut (hValid : MountainValid result)
    (hMarked : BucketMem p.marked source.1.val (Frame.ref source))
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hSourceFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      cut hCut source.1 = source) :
    ∃ (event : Nat) (node : (Frame.ofMountain result).Node),
      event ≤ (Frame.ofMountain result).lastEvent ∧
      (Frame.ofMountain result).eventCut event = cut ∧
      Frame.ref node = physical.outputRef ∧ (Frame.ofMountain result).cell node = physical.cell ∧
      eventFrontier hValid.toOrdered event node.1 = node := by
  have hCutEq := copy.marked_frontier_cut_eq hMarked hCut hSourceFront
  obtain ⟨node, hRef, hCell, _⟩ := physical.frontierAt_source_cut hValid hMarked hCut hSourceFront
  have hRow : (Frame.ofMountain result).height node = cut :=
    (congrArg Cell.row hCell).trans (physical.source_row.trans hCutEq.symm)
  obtain ⟨event, hEvent, hEventRow⟩ := eventCut_of_member
    (mem_eventCuts.mpr (height_mem_eventRows node (hRow.symm ▸ hCut)))
  exact ⟨event, node, hEvent, hEventRow.trans hRow, hRef, hCell,
    frontierAt_of_height_eq hValid.toOrdered ((Frame.ofMountain result).eventCut_one_le event) hEventRow.symm⟩

end PhysicalMarkerRead
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.frontierAt_own_height
#print axioms OmegaY.Geometry.Frame.frontierAt_of_height_eq
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.marked_frontier_cut_eq
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.frontierAt_own_lift_of_marked
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.frontierAt_own_lift_all
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.eventFrontier_own_lift_all
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.actual_event_of_marked_frontier
#print axioms OmegaY.Expansion.PhysicalMarkerRead.frontierAt_source_cut
#print axioms OmegaY.Expansion.PhysicalMarkerRead.actual_event_at_source_cut
