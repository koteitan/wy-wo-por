/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualNonmarkerSplitEvent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSplitEvent

/-!+# Split events with arbitrary preceding marker status

Only the new source frontiers are required to be unmarked. The preceding
frontiers are simultaneously marked or unmarked because they share their
old parent. Marked predecessors use the same complete contour map, obtained
from their true shared reference query. Thus neither old marker status nor
new parent equality is an external assumption.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

private theorem source_marked_index_iff {front : List Nat} {last : Nat}
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

structure EffectiveSameRowEvent {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {u z : (Frame.ofMountain p.reduced).Node}
    (uCopy : EffectiveCopyOccurrence p block start references u result)
    (zCopy : EffectiveCopyOccurrence p block start references z result)
    (hValid : MountainValid result) where
  uNode : (Frame.ofMountain result).Node
  zNode : (Frame.ofMountain result).Node
  event : Nat
  u_ref : Frame.ref uNode = uCopy.outputRef
  z_ref : Frame.ref zNode = zCopy.outputRef
  u_cell : (Frame.ofMountain result).cell uNode = uCopy.read.outputCell
  z_cell : (Frame.ofMountain result).cell zNode = zCopy.read.outputCell
  rows : (Frame.ofMountain result).height uNode = (Frame.ofMountain result).height zNode
  event_end : event ≤ (Frame.ofMountain result).lastEvent
  event_row : (Frame.ofMountain result).eventCut event = (Frame.ofMountain result).height uNode
  u_frontier : eventFrontier hValid.toOrdered event uNode.1 = uNode
  z_frontier : eventFrontier hValid.toOrdered event zNode.1 = zNode

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {u z : (Frame.ofMountain p.reduced).Node}
  (uCopy : EffectiveCopyOccurrence p block start references u result)
  (zCopy : EffectiveCopyOccurrence p block start references z result)

theorem contourCut_function_eq_of_marked_frontiers
    (hUMarked : BucketMem p.marked u.1.val (Frame.ref u))
    (hZMarked : BucketMem p.marked z.1.val (Frame.ref z))
    {sourceCut : Row} (hCut : (1 : Row) ≤ sourceCut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered sourceCut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered sourceCut hCut z.1 = z)
    (cut : Row) : uCopy.contourCut cut = zCopy.contourCut cut := by
  let um := uCopy.data.marker_data uCopy.read.marker uCopy.read.marker_mem
  let zm := zCopy.data.marker_data zCopy.read.marker zCopy.read.marker_mem
  have hiu := uCopy.read.marker_index_of_marked hUMarked
  have hiz := zCopy.read.marker_index_of_marked hZMarked
  have hUCurrent : um.current = (Frame.ofMountain p.reduced).cell u := Option.some.inj
    (um.current_at.symm.trans (by simpa only [hiu] using uCopy.read.source_at))
  have hZCurrent : zm.current = (Frame.ofMountain p.reduced).cell z := Option.some.inj
    (zm.current_at.symm.trans (by simpa only [hiz] using zCopy.read.source_at))
  have hURow : um.current.row = sourceCut := (congrArg Cell.row hUCurrent).trans
    (uCopy.marked_frontier_cut_eq hUMarked hCut hUFront).symm
  have hZRow : zm.current.row = sourceCut := (congrArg Cell.row hZCurrent).trans
    (zCopy.marked_frontier_cut_eq hZMarked hCut hZFront).symm
  have hUQuery : referenceAt start references um.current.row = .ok um.targetCell.row :=
    (uCopy.state.referenceAt_preserved _).symm.trans um.reference
  have hZQuery : referenceAt start references zm.current.row = .ok zm.targetCell.row :=
    (zCopy.state.referenceAt_preserved _).symm.trans zm.reference
  rw [hURow] at hUQuery
  rw [hZRow] at hZQuery
  have hTarget := Except.ok.inj (hUQuery.symm.trans hZQuery)
  change Row.lift um.current.row um.targetCell.row cut = Row.lift zm.current.row zm.targetCell.row cut
  rw [hURow, hZRow, hTarget]

theorem same_row_event (hValid : MountainValid result) (hReal : Real u)
    (hRows : uCopy.read.outputCell.row = zCopy.read.outputCell.row) :
    Nonempty (EffectiveSameRowEvent uCopy zCopy hValid) := by
  let T := Frame.ofMountain result
  obtain ⟨actualU, hURef, hUCell⟩ := Canonical.frame_node_of_cellAt uCopy.output_read
  obtain ⟨actualZ, hZRef, hZCell⟩ := Canonical.frame_node_of_cellAt zCopy.output_read
  have hActualRows : T.height actualU = T.height actualZ :=
    (congrArg Cell.row hUCell).trans (hRows.trans (congrArg Cell.row hZCell).symm)
  have hOne : (1 : Row) ≤ T.height actualU := by
    change (1 : Row) ≤ (T.cell actualU).row
    rw [hUCell]
    exact (Frame.one_le_height (build_normal_of_success p.reduced_build).toOrdered hReal).trans
      uCopy.read.source_row_le_output
  obtain ⟨event, hEvent, hRow⟩ := eventCut_of_member
    (mem_eventCuts.mpr (height_mem_eventRows actualU hOne))
  exact ⟨⟨actualU, actualZ, event, hURef, hZRef, hUCell, hZCell, hActualRows, hEvent, hRow,
    frontierAt_of_height_eq hValid.toOrdered (T.eventCut_one_le event) hRow.symm,
    frontierAt_of_height_eq hValid.toOrdered (T.eventCut_one_le event) (hActualRows.symm.trans hRow.symm)⟩⟩

end EffectiveCopyOccurrence

theorem common_parent_advance_event_of_next_unmarked
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {u z nextU nextZ parent : (Frame.ofMountain p.reduced).Node}
    (uCopy : EffectiveCopyOccurrence p block start references u result)
    (zCopy : EffectiveCopyOccurrence p block start references z result)
    (nextUCopy : EffectiveCopyOccurrence p block start references nextU result)
    (nextZCopy : EffectiveCopyOccurrence p block start references nextZ result)
    (hLast : 1 < last) (hValid : MountainValid result)
    (hNextUUnmarked : nextU.2.val ∉ (p.marked[nextU.1.val]?.getD []).map Ref.index)
    (hNextZUnmarked : nextZ.2.val ∉ (p.marked[nextZ.1.val]?.getD []).map Ref.index)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUUpper : (Frame.ofMountain p.reduced).upper u = some nextU)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some nextZ)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    Nonempty (EffectiveSameRowEvent nextUCopy nextZCopy hValid) := by
  have hIff := p.common_parent_marked_iff_at_cut hUP hZP hCut hUFront hZFront
  by_cases hMarked : BucketMem p.marked u.1.val (Frame.ref u)
  · have hzMarked := hIff.mp hMarked
    have hNormal := build_normal_of_success p.reduced_build
    have hu := frontierAt_spec hNormal.toOrdered hCut u.1
    have hz := frontierAt_spec hNormal.toOrdered hCut z.1
    have hUlow : (Frame.ofMountain p.reduced).height u ≤ cut := hUFront ▸ hu.2.2.1
    have hZlow : (Frame.ofMountain p.reduced).height z ≤ cut := hZFront ▸ hz.2.2.1
    have hSourceSame : (Frame.ofMountain p.reduced).height nextU =
        (Frame.ofMountain p.reduced).height nextZ := by
      rcases le_total ((Frame.ofMountain p.reduced).height z) ((Frame.ofMountain p.reduced).height u) with hle | hle
      · exact hNormal.common_parent_upper_rows hUP hZP hUUpper hZUpper hle
          (hUlow.trans_lt (hz.2.2.2.2 nextZ (hZFront.symm ▸ hZUpper)))
      · exact (hNormal.common_parent_upper_rows hZP hUP hZUpper hUUpper hle
          (hZlow.trans_lt (hu.2.2.2.2 nextU (hUFront.symm ▸ hUUpper)))).symm
    have hRows : nextUCopy.read.outputCell.row = nextZCopy.read.outputCell.row := by
      rw [nextUCopy.read.output_row, nextZCopy.read.output_row]
      change nextUCopy.contourCut ((Frame.ofMountain p.reduced).height nextU) =
        nextZCopy.contourCut ((Frame.ofMountain p.reduced).height nextZ)
      rw [← uCopy.contourCut_eq_of_unmarked_upper nextUCopy hUUpper hNextUUnmarked,
        ← zCopy.contourCut_eq_of_unmarked_upper nextZCopy hZUpper hNextZUnmarked,
        uCopy.contourCut_function_eq_of_marked_frontiers zCopy hMarked hzMarked hCut hUFront hZFront,
        hSourceSame]
    have hReal : Real nextU := by
      have hi := (Frame.upper_spec hUUpper).2
      change 0 < nextU.2.val
      omega
    exact nextUCopy.same_row_event nextZCopy hValid hReal hRows
  · have hNotZ : ¬ BucketMem p.marked z.1.val (Frame.ref z) := fun hz => hMarked (hIff.mpr hz)
    obtain ⟨au, az, event, hUR, hZR, hUC, hZC, hRows, hEvent, hRow, hUF, hZF⟩ :=
      common_parent_advance_event uCopy zCopy nextUCopy nextZCopy hLast hValid
        (fun hu => hMarked ((source_marked_index_iff p u).mp hu))
        (fun hz => hNotZ ((source_marked_index_iff p z).mp hz))
        hNextUUnmarked hNextZUnmarked hUP hZP hUUpper hZUpper hCut hUFront hZFront
    exact ⟨⟨au, az, event, hUR, hZR, hUC, hZC, hRows, hEvent, hRow, hUF, hZF⟩⟩

/-- A genuine next-event depth split now needs marker exclusions only
for the new source frontiers. Both old marker statuses are derived. -/
theorem actual_nonmarker_split_event
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    (hLast : 1 < last) (hValid : MountainValid result)
    (hWidth : 0 < p.reduced.size) {bound event : Nat} (hBound : bound < p.reduced.size)
    (hEvent : event < (Frame.ofMountain p.reduced).lastEvent)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBound : left.val ≤ bound) (hRightBound : right.val ≤ bound)
    (uCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) result)
    (zCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) result)
    (nextUCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) left) result)
    (nextZCopy : EffectiveCopyOccurrence p block start references
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) right) result)
    (hNextUUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) left).2.val ∉
      (p.marked[left.val]?.getD []).map Ref.index)
    (hNextZUnmarked : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered (event + 1) right).2.val ∉
      (p.marked[right.val]?.getD []).map Ref.index)
    {parent : (Frame.ofMountain p.reduced).Node}
    (hLeft : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event left) = some parent)
    (hRight : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered event right) = some parent)
    (hDifferent : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hWidth bound (event + 1)) left.val ≠
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hWidth bound (event + 1)) right.val) :
    Nonempty (EffectiveSameRowEvent nextUCopy nextZCopy hValid) := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨hUUpper, hZUpper⟩ := hNormal.common_parent_depth_split_step hWidth hBound hEvent left right
    hLeftBound hRightBound hLeft hRight hDifferent
  have hu := (eventFrontier_spec hNormal.toOrdered event left).1
  have hz := (eventFrontier_spec hNormal.toOrdered event right).1
  have hnu := (eventFrontier_spec hNormal.toOrdered (event + 1) left).1
  have hnz := (eventFrontier_spec hNormal.toOrdered (event + 1) right).1
  exact common_parent_advance_event_of_next_unmarked uCopy zCopy nextUCopy nextZCopy hLast hValid
    (by simpa only [hnu] using hNextUUnmarked) (by simpa only [hnz] using hNextZUnmarked)
    hLeft hRight hUUpper hZUpper ((Frame.ofMountain p.reduced).eventCut_one_le event)
    (by rw [hu]; rfl) (by rw [hz]; rfl)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.contourCut_function_eq_of_marked_frontiers
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.same_row_event
#print axioms OmegaY.Expansion.common_parent_advance_event_of_next_unmarked
#print axioms OmegaY.Expansion.actual_nonmarker_split_event
