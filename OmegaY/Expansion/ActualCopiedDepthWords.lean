/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCopiedDepthWords.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEarlierTerminalCoverage
import OmegaY.Expansion.ActualBeforeFirstSplit
import OmegaY.Expansion.ActualFirstSplitMarkerBand
import OmegaY.Expansion.ActualFirstSplitComparison
import OmegaY.Expansion.CutDepthWords

/-!
# Complete finite depth-word transport for actual copied columns

Every actual target event above the initial joint contour cut is included.
Equal source tails remain equal. A first strict source difference gives a
real strict target event, and every preceding target event is equal, even
inside newly inserted reference bands. Marked splits use the physical row;
unmarked splits use the common effective upper row.

Strict transport uses recognition only in the completed block-start prefix.
It does not assume recognition of the current copied columns, and is not a
well-foundedness or ordinal-descent theorem.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

private theorem not_marked_index {front : List Nat} {last : Nat}
    (p : Preparation front last) (node : (Frame.ofMountain p.reduced).Node)
    (hNot : ¬ BucketMem p.marked node.1.val (Frame.ref node)) :
    node.2.val ∉ (p.marked[node.1.val]?.getD []).map Ref.index := by
  intro h
  obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
  have he : marker = Frame.ref node := congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
  exact hNot (he ▸ hm)

theorem jointEventCut_one_le {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref}
    {left right : Fin (Frame.ofMountain p.reduced).width}
    (leftCopies : EffectiveEventCopies p block start references ambient left)
    (rightCopies : EffectiveEventCopies p block start references ambient right) (event : Nat) :
    (1 : Row) ≤ jointEventCut leftCopies rightCopies event := by
  exact ((leftCopies event).contourCut_one_le
    ((Frame.ofMountain p.reduced).eventCut_one_le event)
    (eventFrontier_spec (build_normal_of_success p.reduced_build).toOrdered event left).2.2.1).trans
      (le_max_left _ _)

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
  (left right : Fin (Frame.ofMountain p.reduced).width)
  (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
  (hColumn : right.val ≤ left.val)
  (leftCopies : EffectiveEventCopies p block start references ambient left)
  (rightCopies : EffectiveEventCopies p block start references ambient right)
  {previous : Nat}
  (hCommon : (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
    (Frame.ofMountain p.reduced).P
      (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
  (floor : EventCutFloor (Frame.ofMountain ambient) (jointEventCut leftCopies rightCopies previous))

include s history hLast hStartRun hLeftBefore hRightBefore hColumn hCommon

theorem DynamicBlockState.copied_depthWordEq
    (hEnd : previous ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hEqual : Forests.DepthWordEq
      ((Frame.ofMountain p.reduced).frontierForests (bottomCandidateMap (p.reduced.size - 1))
        (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth)
        (p.reduced.size - 1))
      (previous + 1) (Frame.ofMountain p.reduced).lastEvent left.val right.val) :
    Forests.DepthWordEq
      ((Frame.ofMountain ambient).frontierForests (bottomCandidateMap (ambient.size - 1))
        (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) (ambient.size - 1))
      (floor.event + 1) (Frame.ofMountain ambient).lastEvent
      (left.val + block * (p.reduced.size - 1 - p.root.column))
      (right.val + block * (p.reduced.size - 1 - p.root.column)) := by
  apply OmegaY.Expansion.EventCutFloor.depthWordEq_of_above_cut floor s.ambient_valid.toOrdered hTargetWidth
  intro event _ hLow
  exact s.earlier_terminal_coverage history hLast hStartRun hSourceWidth hTargetWidth left right
    hLeftBefore hRightBefore hColumn leftCopies rightCopies hEnd hCommon hEqual hLow.le

theorem DynamicBlockState.copied_depthWordLt
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent)
    (hLess : Forests.DepthWordLt
      ((Frame.ofMountain p.reduced).frontierForests (bottomCandidateMap (p.reduced.size - 1))
        (eventFrontierNat (build_normal_of_success p.reduced_build).toOrdered hSourceWidth)
        (p.reduced.size - 1))
      (previous + 1) (Frame.ofMountain p.reduced).lastEvent left.val right.val) :
    Forests.DepthWordLt
      ((Frame.ofMountain ambient).frontierForests (bottomCandidateMap (ambient.size - 1))
        (eventFrontierNat s.ambient_valid.toOrdered hTargetWidth) (ambient.size - 1))
      (floor.event + 1) (Frame.ofMountain ambient).lastEvent
      (left.val + block * (p.reduced.size - 1 - p.root.column))
      (right.val + block * (p.reduced.size - 1 - p.root.column)) := by
  classical
  obtain ⟨event, hStart, hEnd, hEarlier, hStrict⟩ := hLess
  have hNormal := build_normal_of_success p.reduced_build
  have hLeftColumn := (eventFrontier_spec hNormal.toOrdered event left).1
  have hRightColumn := (eventFrontier_spec hNormal.toOrdered event right).1
  obtain ⟨stable⟩ := s.before_first_split_prefix history hLast hStartRun hSourceWidth hTargetWidth
    left right hLeftBefore hRightBefore hColumn leftCopies rightCopies hStart hEnd hCommon hEarlier
    (ne_of_lt hStrict)
  by_cases hMarked : BucketMem p.marked left.val (Frame.ref (eventFrontier hNormal.toOrdered event left)) ∨
      BucketMem p.marked right.val (Frame.ref (eventFrontier hNormal.toOrdered event right))
  · obtain ⟨targetEvent, hTargetEnd, hRow, hTargetStrict⟩ := s.first_split_marker_physical_event
      history hLast hStartRun hSourceWidth hTargetWidth hKnown left right hLeftBefore hRightBefore
      (leftCopies event) (rightCopies event) hCommon hStart hEnd hEarlier hStrict hMarked
    have hBarrier : (Frame.ofMountain ambient).eventCut targetEvent = stable.leftUpper.row :=
      hRow.trans (stable.upper_row_of_any_marked hLast hMarked).symm
    have hStrict' := hTargetStrict
    simp only [(leftCopies event).source_column, (rightCopies event).source_column,
      hLeftColumn, hRightColumn] at hStrict'
    apply OmegaY.Expansion.EventCutFloor.depthWordLt_of_above_cut floor s.ambient_valid.toOrdered hTargetWidth _ _ _ hTargetEnd
      (stable.joint_below.trans_eq hBarrier.symm) _ hStrict'
    intro earlier hLow hBefore
    apply stable.equal_before earlier hLow.le
    rw [← hBarrier]
    exact ((Frame.ofMountain ambient).eventCut_strict_step (hBefore.trans_le hTargetEnd)).trans_le
      ((Frame.ofMountain ambient).eventCut_monotone (show earlier + 1 ≤ targetEvent by omega))
  · have hLeftUnmarked := not_marked_index p (eventFrontier hNormal.toOrdered event left)
      (show ¬ BucketMem p.marked (eventFrontier hNormal.toOrdered event left).1.val
        (Frame.ref (eventFrontier hNormal.toOrdered event left)) from by
          simpa only [hLeftColumn] using (not_or.mp hMarked).1)
    have hRightUnmarked := not_marked_index p (eventFrontier hNormal.toOrdered event right)
      (show ¬ BucketMem p.marked (eventFrontier hNormal.toOrdered event right).1.val
        (Frame.ref (eventFrontier hNormal.toOrdered event right)) from by
          simpa only [hRightColumn] using (not_or.mp hMarked).2)
    simp only [hLeftColumn] at hLeftUnmarked
    simp only [hRightColumn] at hRightUnmarked
    obtain ⟨split, hTargetStrict⟩ := s.actual_first_split_depth_lt history hLast hStartRun
      hSourceWidth hTargetWidth left right hLeftBefore hRightBefore (leftCopies event) (rightCopies event)
      hLeftUnmarked hRightUnmarked hCommon hStart hEnd hEarlier hStrict
    have hBarrier : (Frame.ofMountain ambient).eventCut split.event = stable.leftUpper.row :=
      split.event_row.trans ((congrArg Cell.row split.u_cell).trans
        (stable.upper_rows_of_unmarked hLast hLeftUnmarked hRightUnmarked).1.symm)
    have hLeftOut : split.uNode.1.val = left.val + block * (p.reduced.size - 1 - p.root.column) := by
      exact (congrArg Ref.column split.u_ref).trans ((leftCopies event).source_column.trans
        (congrArg (fun c => c.val + block * (p.reduced.size - 1 - p.root.column)) hLeftColumn))
    have hRightOut : split.zNode.1.val = right.val + block * (p.reduced.size - 1 - p.root.column) := by
      exact (congrArg Ref.column split.z_ref).trans ((rightCopies event).source_column.trans
        (congrArg (fun c => c.val + block * (p.reduced.size - 1 - p.root.column)) hRightColumn))
    rw [hLeftOut, hRightOut] at hTargetStrict
    apply OmegaY.Expansion.EventCutFloor.depthWordLt_of_above_cut floor s.ambient_valid.toOrdered hTargetWidth _ _ _ split.event_end
      (stable.joint_below.trans_eq hBarrier.symm) _ hTargetStrict
    intro earlier hLow hBefore
    apply stable.equal_before earlier hLow.le
    rw [← hBarrier]
    exact ((Frame.ofMountain ambient).eventCut_strict_step (hBefore.trans_le split.event_end)).trans_le
      ((Frame.ofMountain ambient).eventCut_monotone (show earlier + 1 ≤ split.event by omega))

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.jointEventCut_one_le
#print axioms OmegaY.Expansion.DynamicBlockState.copied_depthWordEq
#print axioms OmegaY.Expansion.DynamicBlockState.copied_depthWordLt
