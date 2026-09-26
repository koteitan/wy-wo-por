/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEarlierTerminalCoverage.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEarlierEventCoverage

/-!
# Equal source suffixes cover the entire actual target tail

After the last source event, both copied source tops remain genuine tops.
Thus the finite shared-cut coverage extends through the final actual
target event, even when unrelated columns have higher events.
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

include s history hLast hStartRun

theorem DynamicBlockState.earlier_terminal_coverage
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (hColumn : right.val ≤ left.val)
    (leftCopies : EffectiveEventCopies p block start references ambient left)
    (rightCopies : EffectiveEventCopies p block start references ambient right)
    {previous event : Nat} (hEnd : previous ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hCommon : (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hEqual : ∀ sourceEvent, previous + 1 ≤ sourceEvent → sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) left.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) right.val)
    (hLow : jointEventCut leftCopies rightCopies previous ≤ (Frame.ofMountain ambient).eventCut event) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (left.val + block * (p.reduced.size - 1 - p.root.column)) =
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (right.val + block * (p.reduced.size - 1 - p.root.column)) := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  by_cases hHigh : T.eventCut event ≤ jointEventCut leftCopies rightCopies F.lastEvent
  · exact s.earlier_event_coverage history hLast hStartRun hSourceWidth hTargetWidth left right
      hLeftBefore hRightBefore hColumn leftCopies rightCopies hEnd le_rfl hCommon hEqual hLow hHigh
  have hTail : jointEventCut leftCopies rightCopies F.lastEvent ≤ T.eventCut event := (lt_of_not_ge hHigh).le
  have hULow : (leftCopies F.lastEvent).read.outputCell.row ≤ T.eventCut event :=
    ((leftCopies F.lastEvent).output_row_le_contourCut
      (eventFrontier_spec hNormal.toOrdered F.lastEvent left).2.2.1).trans ((le_max_left _ _).trans hTail)
  have hZLow : (rightCopies F.lastEvent).read.outputCell.row ≤ T.eventCut event :=
    ((rightCopies F.lastEvent).output_row_le_contourCut
      (eventFrontier_spec hNormal.toOrdered F.lastEvent right).2.2.1).trans ((le_max_right _ _).trans hTail)
  have hUP : F.P (eventFrontier hNormal.toOrdered F.lastEvent left) = none :=
    (hNormal.rawParent_eq_P (eventFrontier_spec hNormal.toOrdered F.lastEvent left).2.1).symm.trans
      (rawParent_none_of_upper_none (eventFrontier_last_upper_none hNormal.toOrdered left))
  have hZP : F.P (eventFrontier hNormal.toOrdered F.lastEvent right) = none :=
    (hNormal.rawParent_eq_P (eventFrontier_spec hNormal.toOrdered F.lastEvent right).2.1).symm.trans
      (rawParent_none_of_upper_none (eventFrontier_last_upper_none hNormal.toOrdered right))
  have hEq := s.copied_depth_eq_at_frontiers_of_source_cut history hLast hStartRun
    hLeftBefore hRightBefore (leftCopies F.lastEvent) (rightCopies F.lastEvent) hSourceWidth hTargetWidth
    (F.eventCut_one_le F.lastEvent) rfl rfl (hUP.trans hZP.symm)
    ((leftCopies F.lastEvent).frontierAt_of_source_parent_none hLast s.ambient_valid
      (eventFrontier_spec hNormal.toOrdered F.lastEvent left).2.1 hUP (T.eventCut_one_le event) hULow)
    ((rightCopies F.lastEvent).frontierAt_of_source_parent_none hLast s.ambient_valid
      (eventFrontier_spec hNormal.toOrdered F.lastEvent right).2.1 hZP (T.eventCut_one_le event) hZLow)
  simpa only [(leftCopies F.lastEvent).source_column, (rightCopies F.lastEvent).source_column,
    (eventFrontier_spec hNormal.toOrdered F.lastEvent left).1,
    (eventFrontier_spec hNormal.toOrdered F.lastEvent right).1] using hEq

theorem DynamicBlockState.actual_earlier_terminal_coverage
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (left right : Fin (Frame.ofMountain p.reduced).width)
    (hLeftRight : p.root.column < left.val) (hRightRight : p.root.column < right.val)
    (hLeftBefore : left.val < next) (hRightBefore : right.val < next)
    (hColumn : right.val ≤ left.val)
    {previous event : Nat} (hEnd : previous ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hCommon : (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hEqual : ∀ sourceEvent, previous + 1 ≤ sourceEvent → sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) left.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) right.val)
    (hLow : jointEventCut (s.eventCopies history hLast left hLeftRight hLeftBefore)
      (s.eventCopies history hLast right hRightRight hRightBefore) previous ≤ (Frame.ofMountain ambient).eventCut event) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (left.val + block * (p.reduced.size - 1 - p.root.column)) =
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (right.val + block * (p.reduced.size - 1 - p.root.column)) :=
  s.earlier_terminal_coverage history hLast hStartRun hSourceWidth hTargetWidth left right
    hLeftBefore hRightBefore hColumn (s.eventCopies history hLast left hLeftRight hLeftBefore)
    (s.eventCopies history hLast right hRightRight hRightBefore) hEnd hCommon hEqual hLow

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.earlier_terminal_coverage
#print axioms OmegaY.Expansion.DynamicBlockState.actual_earlier_terminal_coverage
