/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualBeforeFirstSplit.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEarlierEventCoverage
import OmegaY.Expansion.ActualSplitStableInterval

/-!
# One complete actual prefix before the first source depth difference

Source recovery supplies the last common predecessor parent. All earlier
source intervals and the final stable target interval are then joined.
The resulting strict upper barrier is an actual pair of output upper
reads. A marked new source identifies it with the physical split row;
unmarked new sources identify it with their effective output rows.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

structure FirstSplitStablePrefix {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (hTargetWidth : 0 < ambient.size)
    {left right : Fin (Frame.ofMountain p.reduced).width}
    (leftCopies : EffectiveEventCopies p block start references ambient left)
    (rightCopies : EffectiveEventCopies p block start references ambient right)
    (previous sourceEvent : Nat) where
  before : Nat
  source_event_eq : sourceEvent = before + 1
  before_lower : previous ≤ before
  before_end : before < (Frame.ofMountain p.reduced).lastEvent
  upper_left : (Frame.ofMountain p.reduced).upper
    (eventFrontier (build_normal_of_success p.reduced_build).toOrdered before left) =
      some (eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent left)
  upper_right : (Frame.ofMountain p.reduced).upper
    (eventFrontier (build_normal_of_success p.reduced_build).toOrdered before right) =
      some (eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right)
  source_cut_left : (Frame.ofMountain p.reduced).eventCut sourceEvent = (Frame.ofMountain p.reduced).height
    (eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent left)
  source_cut_right : (Frame.ofMountain p.reduced).eventCut sourceEvent = (Frame.ofMountain p.reduced).height
    (eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right)
  leftUpper : Cell
  rightUpper : Cell
  left_upper_read : Canonical.cellAt ambient
    ⟨(leftCopies before).outputRef.column, (leftCopies before).outputRef.index + 1⟩ = .ok leftUpper
  right_upper_read : Canonical.cellAt ambient
    ⟨(rightCopies before).outputRef.column, (rightCopies before).outputRef.index + 1⟩ = .ok rightUpper
  upper_rows : leftUpper.row = rightUpper.row
  joint_below : jointEventCut leftCopies rightCopies previous < leftUpper.row
  equal_before : ∀ event, jointEventCut leftCopies rightCopies previous ≤ (Frame.ofMountain ambient).eventCut event →
    (Frame.ofMountain ambient).eventCut event < leftUpper.row →
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (left.val + block * (p.reduced.size - 1 - p.root.column)) =
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      (right.val + block * (p.reduced.size - 1 - p.root.column))

theorem DynamicBlockState.before_first_split_prefix
    {front : List Nat} {last : Nat} {p : Preparation front last}
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
    {previous sourceEvent : Nat}
    (hStart : previous + 1 ≤ sourceEvent) (hEnd : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hCommon : (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous left) =
      (Frame.ofMountain p.reduced).P
        (eventFrontier (build_normal_of_success p.reduced_build).toOrdered previous right))
    (hEarlier : ∀ event, previous + 1 ≤ event → event < sourceEvent →
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) event) left.val =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) event) right.val)
    (hDifferent : parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) left.val ≠
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered hSourceWidth
        (p.reduced.size - 1) sourceEvent) right.val) :
    Nonempty (FirstSplitStablePrefix s hTargetWidth leftCopies rightCopies previous sourceEvent) := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hBound : p.reduced.size - 1 < p.reduced.size := by omega
  have hLB : left.val ≤ p.reduced.size - 1 := by have hc : left.val < p.reduced.size := left.isLt; omega
  have hRB : right.val ≤ p.reduced.size - 1 := by have hc : right.val < p.reduced.size := right.isLt; omega
  obtain ⟨before, parent, hEventEq, hBeforeLower, hBeforeEnd, hUP, hZP⟩ :=
    build_first_split_previous_parent p.reduced_build hSourceWidth hBound left right hLB hRB
      hCommon hStart hEnd hEarlier hDifferent
  have hDifferentBefore : parentDepth (eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1)
      (before + 1)) left.val ≠ parentDepth (eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1)
      (before + 1)) right.val := by simpa only [hEventEq] using hDifferent
  obtain ⟨hUUpper, hZUpper⟩ := hNormal.common_parent_depth_split_step hSourceWidth hBound hBeforeEnd
    left right hLB hRB hUP hZP hDifferentBefore
  have hUChanged : eventFrontier hNormal.toOrdered (before + 1) left ≠ eventFrontier hNormal.toOrdered before left := by
    intro he
    have hi := (upper_spec hUUpper).2
    rw [he] at hi
    omega
  have hZChanged : eventFrontier hNormal.toOrdered (before + 1) right ≠ eventFrontier hNormal.toOrdered before right := by
    intro he
    have hi := (upper_spec hZUpper).2
    rw [he] at hi
    omega
  have hSourceLeft := (eventFrontier_advance hNormal.toOrdered hBeforeEnd left hUChanged).2.symm
  have hSourceRight := (eventFrontier_advance hNormal.toOrdered hBeforeEnd right hZChanged).2.symm
  obtain ⟨upperU, upperZ, hReadU, hReadZ, hRows, hBelow, hStable⟩ :=
    s.common_parent_upper_stable_interval history hLast hStartRun hLeftBefore hRightBefore
      (leftCopies before) (rightCopies before) hSourceWidth hTargetWidth hUP hZP hUUpper hZUpper
      (F.eventCut_one_le before) rfl rfl
  refine ⟨{
    before := before
    source_event_eq := hEventEq
    before_lower := hBeforeLower
    before_end := hBeforeEnd
    upper_left := by simpa only [hEventEq] using hUUpper
    upper_right := by simpa only [hEventEq] using hZUpper
    source_cut_left := by simpa only [hEventEq] using hSourceLeft
    source_cut_right := by simpa only [hEventEq] using hSourceRight
    leftUpper := upperU
    rightUpper := upperZ
    left_upper_read := hReadU
    right_upper_read := hReadZ
    upper_rows := hRows
    joint_below := (jointEventCut_monotone leftCopies rightCopies hLast s.ambient_valid hBeforeLower).trans_lt hBelow
    equal_before := ?_ }⟩
  intro event hLow hHigh
  by_cases hBefore : (Frame.ofMountain ambient).eventCut event ≤ jointEventCut leftCopies rightCopies before
  · exact s.earlier_event_coverage history hLast hStartRun hSourceWidth hTargetWidth left right
      hLeftBefore hRightBefore hColumn leftCopies rightCopies hBeforeLower hBeforeEnd.le hCommon
      (fun r hr hrEnd => hEarlier r hr (by omega)) hLow hBefore
  · have hEq := hStable event (le_of_not_ge hBefore) hHigh
    simpa only [(leftCopies before).source_column, (rightCopies before).source_column,
      (eventFrontier_spec hNormal.toOrdered before left).1,
      (eventFrontier_spec hNormal.toOrdered before right).1] using hEq

namespace FirstSplitStablePrefix

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block next : Nat} {start ambient : Mountain} {references : List Ref}
  {s : DynamicBlockState p block start references next ambient} {hTargetWidth : 0 < ambient.size}
  {left right : Fin (Frame.ofMountain p.reduced).width}
  {leftCopies : EffectiveEventCopies p block start references ambient left}
  {rightCopies : EffectiveEventCopies p block start references ambient right}
  {previous sourceEvent : Nat}
  (data : FirstSplitStablePrefix s hTargetWidth leftCopies rightCopies previous sourceEvent)

theorem upper_row_of_any_marked (hLast : 1 < last)
    (hMarked : BucketMem p.marked left.val
        (Frame.ref (eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent left)) ∨
      BucketMem p.marked right.val
        (Frame.ref (eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right))) :
    data.leftUpper.row = (Frame.ofMountain p.reduced).eventCut sourceEvent := by
  have hNormal := build_normal_of_success p.reduced_build
  rcases hMarked with hm | hm
  · obtain ⟨cell, hRead, hRow⟩ := (leftCopies data.before).upper_physical_row_of_marked hLast
      (eventFrontier_spec hNormal.toOrdered data.before left).2.1 data.upper_left hm
    exact (congrArg Cell.row (Except.ok.inj (data.left_upper_read.symm.trans hRead))).trans
      (hRow.trans data.source_cut_left.symm)
  · obtain ⟨cell, hRead, hRow⟩ := (rightCopies data.before).upper_physical_row_of_marked hLast
      (eventFrontier_spec hNormal.toOrdered data.before right).2.1 data.upper_right hm
    exact data.upper_rows.trans
      ((congrArg Cell.row (Except.ok.inj (data.right_upper_read.symm.trans hRead))).trans
        (hRow.trans data.source_cut_right.symm))

theorem upper_rows_of_unmarked (hLast : 1 < last)
    (hLeft : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent left).2.val ∉
      (p.marked[left.val]?.getD []).map Ref.index)
    (hRight : (eventFrontier (build_normal_of_success p.reduced_build).toOrdered sourceEvent right).2.val ∉
      (p.marked[right.val]?.getD []).map Ref.index) :
    data.leftUpper.row = (leftCopies sourceEvent).read.outputCell.row ∧
      data.rightUpper.row = (rightCopies sourceEvent).read.outputCell.row := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨cellL, hReadL, hRowL⟩ := (leftCopies data.before).effective_upper_row_all hLast
    (eventFrontier_spec hNormal.toOrdered data.before left).2.1 (leftCopies sourceEvent) data.upper_left hLeft
  obtain ⟨cellR, hReadR, hRowR⟩ := (rightCopies data.before).effective_upper_row_all hLast
    (eventFrontier_spec hNormal.toOrdered data.before right).2.1 (rightCopies sourceEvent) data.upper_right hRight
  exact ⟨(congrArg Cell.row (Except.ok.inj (data.left_upper_read.symm.trans hReadL))).trans hRowL,
    (congrArg Cell.row (Except.ok.inj (data.right_upper_read.symm.trans hReadR))).trans hRowR⟩

end FirstSplitStablePrefix
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.before_first_split_prefix
#print axioms OmegaY.Expansion.FirstSplitStablePrefix.upper_row_of_any_marked
#print axioms OmegaY.Expansion.FirstSplitStablePrefix.upper_rows_of_unmarked
