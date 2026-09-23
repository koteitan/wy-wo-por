/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEarlierEventCoverage.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentEventInterval
import OmegaY.Expansion.ActualEarlierDepthEquality

/-!
# Actual coverage of every event before a source depth split

Source numerical recovery gives equal designated parents at every earlier
event. A finite crossing argument places any target cut between the first
and last shared cuts into a genuine adjacent source-event interval. The
interval theorem then covers stable contours, changed markers and all
inserted fill events. The optional occurrence family is constructed from
actual recorded column executions, not from target geometry assumptions.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- A finite chain of cuts must cross any cut lying between its endpoints.
The witness is an actual adjacent pair, even if some cuts are repeated. -/
theorem row_interval_adjacent (cuts : Nat → Row) {first last : Nat} {cut : Row}
    (hOrder : first < last) (hLow : cuts first ≤ cut) (hHigh : cut ≤ cuts last) :
    ∃ index, first ≤ index ∧ index < last ∧ cuts index ≤ cut ∧ cut ≤ cuts (index + 1) := by
  classical
  let eligible := (Finset.range last).filter fun index => first ≤ index ∧ cuts index ≤ cut
  have hNonempty : eligible.Nonempty :=
    ⟨first, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hOrder, le_rfl, hLow⟩⟩
  let chosen := eligible.max' hNonempty
  have hm := Finset.mem_filter.mp (Finset.max'_mem eligible hNonempty)
  have hb := Finset.mem_range.mp hm.1
  refine ⟨chosen, hm.2.1, hb, hm.2.2, ?_⟩
  by_cases he : chosen + 1 = last
  · exact he ▸ hHigh
  · have hNext : chosen + 1 < last := by omega
    by_contra hn
    have hMember : chosen + 1 ∈ eligible := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hNext, by have := hm.2.1; omega, (lt_of_not_ge hn).le⟩
    have hBound : chosen + 1 ≤ chosen := Finset.le_max' eligible _ hMember
    omega

abbrev EffectiveEventCopies {front : List Nat} {last : Nat} (p : Preparation front last)
    (block : Nat) (start : Mountain) (references : List Ref) (ambient : Mountain)
    (column : Fin (Frame.ofMountain p.reduced).width) :=
  (event : Nat) → EffectiveCopyOccurrence p block start references
    (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event column) ambient

noncomputable def jointEventCut {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    {left right : Fin (Frame.ofMountain p.reduced).width}
    (leftCopies : EffectiveEventCopies p block start references ambient left)
    (rightCopies : EffectiveEventCopies p block start references ambient right) (event : Nat) : Row :=
  max ((leftCopies event).contourCut ((Frame.ofMountain p.reduced).eventCut event))
    ((rightCopies event).contourCut ((Frame.ofMountain p.reduced).eventCut event))

theorem jointEventCut_monotone {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    {left right : Fin (Frame.ofMountain p.reduced).width}
    (leftCopies : EffectiveEventCopies p block start references ambient left)
    (rightCopies : EffectiveEventCopies p block start references ambient right)
    (hLast : 1 < last) (hValid : MountainValid ambient) :
    Monotone (jointEventCut leftCopies rightCopies) := by
  intro first last hOrder
  apply max_le_max
  · exact (leftCopies first).contourCut_le_of_frontiers (leftCopies last) hLast hValid rfl
      ((Frame.ofMountain p.reduced).eventCut_one_le first) ((Frame.ofMountain p.reduced).eventCut_one_le last)
      ((Frame.ofMountain p.reduced).eventCut_monotone hOrder) rfl rfl
  · exact (rightCopies first).contourCut_le_of_frontiers (rightCopies last) hLast hValid rfl
      ((Frame.ofMountain p.reduced).eventCut_one_le first) ((Frame.ofMountain p.reduced).eventCut_one_le last)
      ((Frame.ofMountain p.reduced).eventCut_monotone hOrder) rfl rfl

noncomputable def DynamicBlockState.eventCopies
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (column : Fin (Frame.ofMountain p.reduced).width)
    (hRight : p.root.column < column.val) (hBefore : column.val < next) :
    EffectiveEventCopies p block start references ambient column := fun event =>
  Classical.choice (s.prior_effective_occurrence history hLast
    (source := eventFrontier (build_normal_of_success p.reduced_build).toOrdered event column) hRight hBefore)

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

theorem DynamicBlockState.earlier_event_coverage
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (hColumn : right.val ≤ left.val)
    (leftCopies : EffectiveEventCopies p block start references ambient left)
    (rightCopies : EffectiveEventCopies p block start references ambient right)
    {previous through event : Nat}
    (hOrder : previous ≤ through) (hEnd : through ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hCommon : (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hEqual : ∀ sourceEvent, previous + 1 ≤ sourceEvent → sourceEvent ≤ through →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) left.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) right.val)
    (hLow : jointEventCut leftCopies rightCopies previous ≤ (Frame.ofMountain ambient).eventCut event)
    (hHigh : (Frame.ofMountain ambient).eventCut event ≤ jointEventCut leftCopies rightCopies through) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (left.val + block * (p.reduced.size - 1 - p.root.column)) =
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (right.val + block * (p.reduced.size - 1 - p.root.column)) := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hParents : ∀ index, previous ≤ index → index ≤ through →
      F.P (eventFrontier hNormal.toOrdered index left) = F.P (eventFrontier hNormal.toOrdered index right) := by
    intro index hPrevious hThrough
    by_cases he : index = previous
    · exact he ▸ hCommon
    · exact build_source_parent_eq_after_equal_depths p.reduced_build hSourceWidth left right
        hCommon (by omega) (hThrough.trans hEnd)
        (fun r hr hre => hEqual r hr (by omega)) (hEqual index (by omega) hThrough)
  by_cases he : previous = through
  · have hPoint : T.eventCut event = jointEventCut leftCopies rightCopies previous :=
      le_antisymm (by simpa only [← he] using hHigh) hLow
    let u := eventFrontier hNormal.toOrdered previous left
    let z := eventFrontier hNormal.toOrdered previous right
    have hCut := F.eventCut_one_le previous
    have hTargetCut := T.eventCut_one_le event
    have hULow : (leftCopies previous).read.outputCell.row ≤ T.eventCut event :=
      ((leftCopies previous).output_row_le_contourCut
        (eventFrontier_spec hNormal.toOrdered previous left).2.2.1).trans ((le_max_left _ _).trans hLow)
    have hZLow : (rightCopies previous).read.outputCell.row ≤ T.eventCut event :=
      ((rightCopies previous).output_row_le_contourCut
        (eventFrontier_spec hNormal.toOrdered previous right).2.2.1).trans ((le_max_right _ _).trans hLow)
    have hActual :
        (∃ node : T.Node, Frame.ref node = (leftCopies previous).outputRef ∧
          eventFrontier s.ambient_valid.toOrdered event node.1 = node) ∧
        (∃ node : T.Node, Frame.ref node = (rightCopies previous).outputRef ∧
          eventFrontier s.ambient_valid.toOrdered event node.1 = node) := by
      cases hParent : F.P u with
      | none =>
          exact ⟨(leftCopies previous).frontierAt_of_source_parent_none hLast s.ambient_valid
            (eventFrontier_spec hNormal.toOrdered previous left).2.1 hParent hTargetCut hULow,
            (rightCopies previous).frontierAt_of_source_parent_none hLast s.ambient_valid
            (eventFrontier_spec hNormal.toOrdered previous right).2.1
            (hCommon.symm.trans hParent) hTargetCut hZLow⟩
      | some parent =>
          obtain ⟨shared⟩ := (leftCopies previous).shared_contour_frontier_all (rightCopies previous)
            hLast s.ambient_valid hParent (hCommon.symm.trans hParent) hCut rfl rfl
          refine ⟨⟨shared.uNode, shared.u_ref, ?_⟩, ⟨shared.zNode, shared.z_ref, ?_⟩⟩
          · exact frontierAt_of_lower_cut s.ambient_valid.toOrdered hTargetCut shared.shared_cut_one shared.u_shared
              ((congrArg Cell.row shared.u_cell).le.trans hULow) hPoint.le
          · exact frontierAt_of_lower_cut s.ambient_valid.toOrdered hTargetCut shared.shared_cut_one shared.z_shared
              ((congrArg Cell.row shared.z_cell).le.trans hZLow) hPoint.le
    have hEq := s.copied_depth_eq_at_frontiers_of_source_cut history hLast hStartRun
      hLeftBefore hRightBefore (leftCopies previous) (rightCopies previous) hSourceWidth hTargetWidth
      hCut rfl rfl hCommon hActual.1 hActual.2
    simpa only [(leftCopies previous).source_column, (rightCopies previous).source_column,
      (eventFrontier_spec hNormal.toOrdered previous left).1,
      (eventFrontier_spec hNormal.toOrdered previous right).1] using hEq
  · obtain ⟨index, hFirst, hLastIndex, hLowIndex, hHighIndex⟩ :=
      row_interval_adjacent (jointEventCut leftCopies rightCopies) (by omega) hLow hHigh
    have hEq := s.common_parent_event_interval_depth_eq history hLast hStartRun
      hLeftBefore hRightBefore hColumn (leftCopies index) (rightCopies index)
      (leftCopies (index + 1)) (rightCopies (index + 1)) hSourceWidth hTargetWidth
      (hLastIndex.trans_le hEnd) rfl rfl rfl rfl (hParents index hFirst hLastIndex.le)
      (hParents (index + 1) (by omega) (by omega)) hLowIndex hHighIndex
    simpa only [(leftCopies index).source_column, (rightCopies index).source_column,
      (eventFrontier_spec hNormal.toOrdered index left).1,
      (eventFrontier_spec hNormal.toOrdered index right).1] using hEq

/-- The shared-cut family is chosen solely from recorded copy executions.
The caller supplies source equal-depth data and bounds on these genuine
cuts; no copied frontier, parent, or intermediate-event premise is used. -/
theorem DynamicBlockState.actual_earlier_event_coverage
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftRight : p.root.column < left.val) (hRightRight : p.root.column < right.val)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (hColumn : right.val ≤ left.val)
    {previous through event : Nat}
    (hOrder : previous ≤ through) (hEnd : through ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hCommon : (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hEqual : ∀ sourceEvent, previous + 1 ≤ sourceEvent → sourceEvent ≤ through →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) left.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) right.val)
    (hLow : jointEventCut (s.eventCopies history hLast left hLeftRight hLeftBefore)
      (s.eventCopies history hLast right hRightRight hRightBefore) previous ≤ (Frame.ofMountain ambient).eventCut event)
    (hHigh : (Frame.ofMountain ambient).eventCut event ≤
      jointEventCut (s.eventCopies history hLast left hLeftRight hLeftBefore)
        (s.eventCopies history hLast right hRightRight hRightBefore) through) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (left.val + block * (p.reduced.size - 1 - p.root.column)) =
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (right.val + block * (p.reduced.size - 1 - p.root.column)) :=
  s.earlier_event_coverage history hLast hStartRun hSourceWidth hTargetWidth left right
    hLeftBefore hRightBefore hColumn (s.eventCopies history hLast left hLeftRight hLeftBefore)
    (s.eventCopies history hLast right hRightRight hRightBefore) hOrder hEnd hCommon hEqual hLow hHigh

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.row_interval_adjacent
#print axioms OmegaY.Expansion.jointEventCut_monotone
#print axioms OmegaY.Expansion.DynamicBlockState.eventCopies
#print axioms OmegaY.Expansion.DynamicBlockState.earlier_event_coverage
#print axioms OmegaY.Expansion.DynamicBlockState.actual_earlier_event_coverage
