/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCommonParentEventInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CommonParentEventTransition

/-!
# Full actual target-event intervals across adjacent source events

The source frame decides whether both frontiers stay or both advance.
The target interval uses the maxima of the two actual own contour cuts
at its endpoints. Every actual event in this closed interval has equal
depth if the source parents agree at both source events. Neither target
frontiers nor a description of inserted events is an input.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

private theorem marked_index_iff {front : List Nat} {last : Nat}
    (p : Preparation front last) (node : (Frame.ofMountain p.reduced).Node) :
    node.2.val ∈ (p.marked[node.1.val]?.getD []).map Ref.index ↔
      BucketMem p.marked node.1.val (Frame.ref node) := by
  constructor
  · intro h
    obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
    have he : marker = Frame.ref node := congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
    exact he ▸ hm
  · intro h
    exact List.mem_map.mpr ⟨Frame.ref node, h, rfl⟩

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}

theorem frontierAt_of_source_parent_none {source : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last) (hValid : MountainValid result) (hReal : Real source)
    (hNone : (Frame.ofMountain p.reduced).P source = none)
    {cut : Row} (hCut : (1 : Row) ≤ cut) (hBelow : copy.read.outputCell.row ≤ cut) :
    ∃ node : (Frame.ofMountain result).Node, Frame.ref node = copy.outputRef ∧
      frontierAt hValid.toOrdered cut hCut node.1 = node := by
  have hTop : (Frame.ofMountain p.reduced).upper source = none := by
    cases hUpper : (Frame.ofMountain p.reduced).upper source with
    | none => rfl
    | some upper =>
        obtain ⟨parent, hParent, _⟩ := (build_normal_of_success p.reduced_build).upper_step source upper hReal hUpper
        rw [hNone] at hParent
        cases hParent
  obtain ⟨node, hRef, hCell⟩ := Canonical.frame_node_of_cellAt copy.output_read
  refine ⟨node, hRef, frontierAt_eq_of_upper_barrier hValid.toOrdered hCut
    ((congrArg Cell.row hCell).le.trans hBelow) ?_⟩
  intro upper hUpper
  rw [copy.top_upper_none hLast hTop hRef] at hUpper
  cases hUpper

end EffectiveCopyOccurrence

/-- A moving common-parent step has one effective output row at its end,
even if both new nodes are markers. The none-parent case cannot be marked.
This derives the endpoint identity from actual occurrence queries. -/
theorem common_parent_advance_output_rows
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {u z nextU nextZ parent : (Frame.ofMountain p.reduced).Node}
    (uCopy : EffectiveCopyOccurrence p block start references u result)
    (zCopy : EffectiveCopyOccurrence p block start references z result)
    (nextUCopy : EffectiveCopyOccurrence p block start references nextU result)
    (nextZCopy : EffectiveCopyOccurrence p block start references nextZ result)
    (hLast : 1 < last) (hValid : MountainValid result)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUUpper : (Frame.ofMountain p.reduced).upper u = some nextU)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some nextZ)
    {cut nextCut : Row} (hCut : (1 : Row) ≤ cut) (hNextCut : (1 : Row) ≤ nextCut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z)
    (hNextUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered nextCut hNextCut nextU.1 = nextU)
    (hNextZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered nextCut hNextCut nextZ.1 = nextZ)
    (hCommon : (Frame.ofMountain p.reduced).P nextU = (Frame.ofMountain p.reduced).P nextZ) :
    nextUCopy.read.outputCell.row = nextZCopy.read.outputCell.row := by
  have hNormal := build_normal_of_success p.reduced_build
  have hUReal : Real nextU := hNextUFront ▸ (frontierAt_spec hNormal.toOrdered hNextCut nextU.1).2.1
  have hZReal : Real nextZ := hNextZFront ▸ (frontierAt_spec hNormal.toOrdered hNextCut nextZ.1).2.1
  have hMarkedIff : BucketMem p.marked nextU.1.val (Frame.ref nextU) ↔
      BucketMem p.marked nextZ.1.val (Frame.ref nextZ) := by
    constructor
    · intro hm
      obtain ⟨father, hFather⟩ := nextUCopy.source_parent_some_of_marked hUReal hm
      exact (p.common_parent_marked_iff_at_cut hFather (hCommon.symm.trans hFather)
        hNextCut hNextUFront hNextZFront).mp hm
    · intro hm
      obtain ⟨father, hFather⟩ := nextZCopy.source_parent_some_of_marked hZReal hm
      exact (p.common_parent_marked_iff_at_cut (hCommon.trans hFather) hFather
        hNextCut hNextUFront hNextZFront).mpr hm
  by_cases hm : BucketMem p.marked nextU.1.val (Frame.ref nextU)
  · have hz := hMarkedIff.mp hm
    have huRow := nextUCopy.marked_frontier_cut_eq hm hNextCut hNextUFront
    have hzRow := nextZCopy.marked_frontier_cut_eq hz hNextCut hNextZFront
    have hSame := nextUCopy.contourCut_eq_of_marked_frontiers nextZCopy hm hz hNextCut hNextUFront hNextZFront
    calc
      nextUCopy.read.outputCell.row = nextUCopy.contourCut nextCut := by rw [nextUCopy.read.output_row, huRow]; rfl
      _ = nextZCopy.contourCut nextCut := hSame
      _ = nextZCopy.read.outputCell.row := by rw [nextZCopy.read.output_row, hzRow]; rfl
  · obtain ⟨data⟩ := common_parent_advance_event_of_next_unmarked uCopy zCopy nextUCopy nextZCopy hLast hValid
      (fun hi => hm ((marked_index_iff p nextU).mp hi))
      (fun hi => hm (hMarkedIff.mpr ((marked_index_iff p nextZ).mp hi)))
      hUP hZP hUUpper hZUpper hCut hUFront hZFront
    exact (congrArg Cell.row data.u_cell).symm.trans (data.rows.trans (congrArg Cell.row data.z_cell))

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

theorem DynamicBlockState.common_parent_event_interval_depth_eq
    {u z nextU nextZ : (Frame.ofMountain p.reduced).Node}
    (hUBefore : u.1.val < next) (hZBefore : z.1.val < next)
    (hColumn : z.1.val ≤ u.1.val)
    (uCopy : EffectiveCopyOccurrence p block start references u ambient)
    (zCopy : EffectiveCopyOccurrence p block start references z ambient)
    (nextUCopy : EffectiveCopyOccurrence p block start references nextU ambient)
    (nextZCopy : EffectiveCopyOccurrence p block start references nextZ ambient)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    {sourceEvent event : Nat} (hEvent : sourceEvent < (Frame.ofMountain p.reduced).lastEvent)
    (hUFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent u.1 = u)
    (hZFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent z.1 = z)
    (hNextUFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered (sourceEvent + 1) u.1 = nextU)
    (hNextZFront : eventFrontier (build_normal_of_success p.reduced_build).toOrdered (sourceEvent + 1) z.1 = nextZ)
    (hCommon : (Frame.ofMountain p.reduced).P u = (Frame.ofMountain p.reduced).P z)
    (hNextCommon : (Frame.ofMountain p.reduced).P nextU = (Frame.ofMountain p.reduced).P nextZ)
    (hLow : max (uCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent))
      (zCopy.contourCut ((Frame.ofMountain p.reduced).eventCut sourceEvent)) ≤
        (Frame.ofMountain ambient).eventCut event)
    (hHigh : (Frame.ofMountain ambient).eventCut event ≤
      max (nextUCopy.contourCut ((Frame.ofMountain p.reduced).eventCut (sourceEvent + 1)))
        (nextZCopy.contourCut ((Frame.ofMountain p.reduced).eventCut (sourceEvent + 1)))) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      uCopy.outputRef.column =
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      zCopy.outputRef.column := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hCut := F.eventCut_one_le sourceEvent
  have hNextCut := F.eventCut_one_le (sourceEvent + 1)
  have hTargetCut := T.eventCut_one_le event
  have hUReal : Real u := hUFront ▸ (eventFrontier_spec hNormal.toOrdered sourceEvent u.1).2.1
  have hZReal : Real z := hZFront ▸ (eventFrontier_spec hNormal.toOrdered sourceEvent z.1).2.1
  have hUBelow : F.height u ≤ F.eventCut sourceEvent :=
    hUFront ▸ (eventFrontier_spec hNormal.toOrdered sourceEvent u.1).2.2.1
  have hZBelow : F.height z ≤ F.eventCut sourceEvent :=
    hZFront ▸ (eventFrontier_spec hNormal.toOrdered sourceEvent z.1).2.2.1
  have hULow := (uCopy.output_row_le_contourCut hUBelow).trans ((le_max_left _ _).trans hLow)
  have hZLow := (zCopy.output_row_le_contourCut hZBelow).trans ((le_max_right _ _).trans hLow)
  cases hParent : F.P u with
  | none =>
      exact s.copied_depth_eq_at_frontiers_of_source_cut history hLast hStartRun hUBefore hZBefore
        uCopy zCopy hSourceWidth hTargetWidth hCut hUFront hZFront hCommon
        (uCopy.frontierAt_of_source_parent_none hLast s.ambient_valid hUReal hParent hTargetCut hULow)
        (zCopy.frontierAt_of_source_parent_none hLast s.ambient_valid hZReal
          (hCommon.symm.trans hParent) hTargetCut hZLow)
  | some parent =>
      have hMoves := hNormal.common_parent_move_or_stay hEvent u.1 z.1
        (by rw [hUFront]; exact hParent) (by rw [hZFront]; exact hCommon.symm.trans hParent)
      simp only [hUFront, hZFront, hNextUFront, hNextZFront] at hMoves
      rcases hMoves with ⟨hUStay, hZStay⟩ | ⟨hUUpper, hZUpper, hUCut, hZCut⟩
      · have hUCopyCut : uCopy.contourCut (F.eventCut (sourceEvent + 1)) =
            nextUCopy.contourCut (F.eventCut (sourceEvent + 1)) := by
          cases hUStay
          exact uCopy.contourCut_unique nextUCopy _
        have hZCopyCut : zCopy.contourCut (F.eventCut (sourceEvent + 1)) =
            nextZCopy.contourCut (F.eventCut (sourceEvent + 1)) := by
          cases hZStay
          exact zCopy.contourCut_unique nextZCopy _
        change T.eventCut event ≤ max (nextUCopy.contourCut (F.eventCut (sourceEvent + 1)))
          (nextZCopy.contourCut (F.eventCut (sourceEvent + 1))) at hHigh
        rw [← hUCopyCut, ← hZCopyCut] at hHigh
        obtain ⟨shared⟩ := uCopy.shared_contour_frontier_all zCopy hLast s.ambient_valid
          hParent (hCommon.symm.trans hParent) hNextCut
          (hNextUFront.trans hUStay) (hNextZFront.trans hZStay)
        have hAU : ∃ node : T.Node, Frame.ref node = uCopy.outputRef ∧
            eventFrontier s.ambient_valid.toOrdered event node.1 = node :=
          ⟨shared.uNode, shared.u_ref, frontierAt_of_lower_cut s.ambient_valid.toOrdered
            hTargetCut shared.shared_cut_one shared.u_shared
            ((congrArg Cell.row shared.u_cell).le.trans hULow) hHigh⟩
        have hAZ : ∃ node : T.Node, Frame.ref node = zCopy.outputRef ∧
            eventFrontier s.ambient_valid.toOrdered event node.1 = node :=
          ⟨shared.zNode, shared.z_ref, frontierAt_of_lower_cut s.ambient_valid.toOrdered
            hTargetCut shared.shared_cut_one shared.z_shared
            ((congrArg Cell.row shared.z_cell).le.trans hZLow) hHigh⟩
        exact s.copied_depth_eq_at_frontiers_of_source_cut history hLast hStartRun hUBefore hZBefore
          uCopy zCopy hSourceWidth hTargetWidth hCut hUFront hZFront hCommon hAU hAZ
      · have hUColumn : nextU.1 = u.1 := (Frame.upper_spec hUUpper).1
        have hZColumn : nextZ.1 = z.1 := (Frame.upper_spec hZUpper).1
        have hNextUF : frontierAt hNormal.toOrdered (F.eventCut (sourceEvent + 1)) hNextCut nextU.1 = nextU := by
          rw [hUColumn]; exact hNextUFront
        have hNextZF : frontierAt hNormal.toOrdered (F.eventCut (sourceEvent + 1)) hNextCut nextZ.1 = nextZ := by
          rw [hZColumn]; exact hNextZFront
        have hRows := common_parent_advance_output_rows uCopy zCopy nextUCopy nextZCopy hLast s.ambient_valid
          hParent (hCommon.symm.trans hParent) hUUpper hZUpper hCut hNextCut
          hUFront hZFront hNextUF hNextZF hNextCommon
        have hUOwn : nextUCopy.contourCut (F.eventCut (sourceEvent + 1)) = nextUCopy.read.outputCell.row := by
          rw [hUCut]; exact nextUCopy.read.output_row.symm
        have hZOwn : nextZCopy.contourCut (F.eventCut (sourceEvent + 1)) = nextZCopy.read.outputCell.row := by
          rw [hZCut]; exact nextZCopy.read.output_row.symm
        have hHighRow : T.eventCut event ≤ nextUCopy.read.outputCell.row := by
          change T.eventCut event ≤ max (nextUCopy.contourCut (F.eventCut (sourceEvent + 1)))
            (nextZCopy.contourCut (F.eventCut (sourceEvent + 1))) at hHigh
          simpa only [hUOwn, hZOwn, ← hRows, max_self] using hHigh
        exact s.common_parent_upper_interval_depth_eq history hLast hStartRun hUBefore hZBefore hColumn
          uCopy zCopy nextUCopy nextZCopy hSourceWidth hTargetWidth hParent (hCommon.symm.trans hParent)
          hUUpper hZUpper hCut hUFront hZFront hNextCommon (max_le hULow hZLow) hHighRow

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.frontierAt_of_source_parent_none
#print axioms OmegaY.Expansion.common_parent_advance_output_rows
#print axioms OmegaY.Expansion.DynamicBlockState.common_parent_event_interval_depth_eq
