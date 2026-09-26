/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCommonParentStepInterval.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCommonParentInterval

/-!
# Every target event across a common-parent source upper step

Both the old and new source parents agree. The copied stable part,
possible physical-marker fill, and effective endpoint exhaust the closed
interval stated below, including when the controlling marker changes.
There is no assumption about intermediate target frontiers or depths.
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

theorem DynamicBlockState.common_parent_upper_interval_depth_eq
    {u z nextU nextZ parent : (Frame.ofMountain p.reduced).Node}
    (hUBefore : u.1.val < next) (hZBefore : z.1.val < next)
    (hColumn : z.1.val ≤ u.1.val)
    (uCopy : EffectiveCopyOccurrence p block start references u ambient)
    (zCopy : EffectiveCopyOccurrence p block start references z ambient)
    (nextUCopy : EffectiveCopyOccurrence p block start references nextU ambient)
    (nextZCopy : EffectiveCopyOccurrence p block start references nextZ ambient)
    (hSourceWidth : 0 < p.reduced.size) (hTargetWidth : 0 < ambient.size)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUUpper : (Frame.ofMountain p.reduced).upper u = some nextU)
    (hZUpper : (Frame.ofMountain p.reduced).upper z = some nextZ)
    {sourceCut : Row} (hCut : (1 : Row) ≤ sourceCut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered sourceCut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered sourceCut hCut z.1 = z)
    (hNextCommon : (Frame.ofMountain p.reduced).P nextU = (Frame.ofMountain p.reduced).P nextZ)
    {event : Nat}
    (hLow : max uCopy.read.outputCell.row zCopy.read.outputCell.row ≤
      (Frame.ofMountain ambient).eventCut event)
    (hHigh : (Frame.ofMountain ambient).eventCut event ≤ nextUCopy.read.outputCell.row) :
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      uCopy.outputRef.column =
    parentDepth (eventParentMap s.ambient_valid.toOrdered hTargetWidth (ambient.size - 1) event)
      zCopy.outputRef.column := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hu := frontierAt_spec hNormal.toOrdered hCut u.1
  have hz := frontierAt_spec hNormal.toOrdered hCut z.1
  have hUReal : Real u := hUFront ▸ hu.2.1
  have hZReal : Real z := hZFront ▸ hz.2.1
  have hULow : F.height u ≤ sourceCut := hUFront ▸ hu.2.2.1
  have hZLow : F.height z ≤ sourceCut := hZFront ▸ hz.2.2.1
  have hSourceRows : F.height nextU = F.height nextZ := by
    rcases le_total (F.height z) (F.height u) with hle | hle
    · exact hNormal.common_parent_upper_rows hUP hZP hUUpper hZUpper hle
        (hULow.trans_lt (hz.2.2.2.2 nextZ (hZFront.symm ▸ hZUpper)))
    · exact (hNormal.common_parent_upper_rows hZP hUP hZUpper hUUpper hle
        (hZLow.trans_lt (hu.2.2.2.2 nextU (hUFront.symm ▸ hUUpper)))).symm
  have hNextUReal : Real nextU := by
    have hi := (Frame.upper_spec hUUpper).2
    change 0 < nextU.2.val
    omega
  have hNextZReal : Real nextZ := by
    have hi := (Frame.upper_spec hZUpper).2
    change 0 < nextZ.2.val
    omega
  have hNextCut : (1 : Row) ≤ F.height nextU := Frame.one_le_height hNormal.toOrdered hNextUReal
  have hNextUFront : frontierAt hNormal.toOrdered (F.height nextU) hNextCut nextU.1 = nextU :=
    frontierAt_of_height_eq hNormal.toOrdered hNextCut rfl
  have hNextZFront : frontierAt hNormal.toOrdered (F.height nextU) hNextCut nextZ.1 = nextZ :=
    frontierAt_of_height_eq hNormal.toOrdered hNextCut hSourceRows.symm
  have hNextUColumn : nextU.1.val = u.1.val := congrArg Fin.val (Frame.upper_spec hUUpper).1
  have hNextZColumn : nextZ.1.val = z.1.val := congrArg Fin.val (Frame.upper_spec hZUpper).1
  have hUOutputColumn : nextUCopy.outputRef.column = uCopy.outputRef.column := by
    rw [nextUCopy.source_column, uCopy.source_column, hNextUColumn]
  have hZOutputColumn : nextZCopy.outputRef.column = zCopy.outputRef.column := by
    rw [nextZCopy.source_column, zCopy.source_column, hNextZColumn]
  have hMarkedIff : BucketMem p.marked nextU.1.val (Frame.ref nextU) ↔
      BucketMem p.marked nextZ.1.val (Frame.ref nextZ) := by
    cases hParent : F.P nextU with
    | none =>
        apply iff_of_false
        · intro hm
          obtain ⟨father, hFather⟩ := nextUCopy.source_parent_some_of_marked hNextUReal hm
          rw [hParent] at hFather
          cases hFather
        · intro hm
          obtain ⟨father, hFather⟩ := nextZCopy.source_parent_some_of_marked hNextZReal hm
          rw [hNextCommon.symm, hParent] at hFather
          cases hFather
    | some father =>
        exact p.common_parent_marked_iff_at_cut hParent (hNextCommon.symm.trans hParent)
          hNextCut hNextUFront hNextZFront
  have hOutputRows : nextUCopy.read.outputCell.row = nextZCopy.read.outputCell.row := by
    by_cases hm : BucketMem p.marked nextU.1.val (Frame.ref nextU)
    · have hSame := nextUCopy.contourCut_eq_of_marked_frontiers nextZCopy hm (hMarkedIff.mp hm)
        hNextCut hNextUFront hNextZFront
      calc
        nextUCopy.read.outputCell.row = nextUCopy.contourCut (F.height nextU) := nextUCopy.read.output_row
        _ = nextZCopy.contourCut (F.height nextU) := hSame
        _ = nextZCopy.read.outputCell.row := by rw [hSourceRows]; exact nextZCopy.read.output_row.symm
    · have hnu := fun hi => hm ((marked_index_iff p nextU).mp hi)
      have hnz := fun hi => hm (hMarkedIff.mpr ((marked_index_iff p nextZ).mp hi))
      obtain ⟨data⟩ := common_parent_advance_event_of_next_unmarked uCopy zCopy nextUCopy nextZCopy
        hLast s.ambient_valid hnu hnz hUP hZP hUUpper hZUpper hCut hUFront hZFront
      exact (congrArg Cell.row data.u_cell).symm.trans (data.rows.trans (congrArg Cell.row data.z_cell))
  have hEventCut := T.eventCut_one_le event
  have hULower : uCopy.read.outputCell.row ≤ T.eventCut event := (le_max_left _ _).trans hLow
  have hZLower : zCopy.read.outputCell.row ≤ T.eventCut event := (le_max_right _ _).trans hLow
  by_cases hEndpoint : T.eventCut event = nextUCopy.read.outputCell.row
  · have hEq := s.copied_depth_eq_at_frontiers_of_source_cut history hLast hStartRun
      (hNextUColumn ▸ hUBefore) (hNextZColumn ▸ hZBefore) nextUCopy nextZCopy hSourceWidth hTargetWidth
      hNextCut hNextUFront hNextZFront hNextCommon
      (nextUCopy.frontierAt_at_output_row s.ambient_valid hEventCut hEndpoint.symm)
      (nextZCopy.frontierAt_at_output_row s.ambient_valid hEventCut (hOutputRows.symm.trans hEndpoint.symm))
    simpa only [hUOutputColumn, hZOutputColumn] using hEq
  have hBelowTarget : T.eventCut event < nextUCopy.read.outputCell.row := lt_of_le_of_ne hHigh hEndpoint
  by_cases hMarked : BucketMem p.marked nextU.1.val (Frame.ref nextU)
  · have hzMarked := hMarkedIff.mp hMarked
    by_cases hBeforePhysical : T.eventCut event < F.height nextU
    · obtain ⟨upperU, hReadU, hRowU⟩ := uCopy.upper_physical_row_of_marked hLast hUReal hUUpper hMarked
      obtain ⟨upperZ, hReadZ, hRowZ⟩ := zCopy.upper_physical_row_of_marked hLast hZReal hZUpper hzMarked
      exact s.copied_depth_eq_at_frontiers_of_source_cut history hLast hStartRun hUBefore hZBefore
        uCopy zCopy hSourceWidth hTargetWidth hCut hUFront hZFront (hUP.trans hZP.symm)
        (uCopy.frontierAt_of_upper_read s.ambient_valid hEventCut hReadU hULower (hBeforePhysical.trans_eq hRowU.symm))
        (zCopy.frontierAt_of_upper_read s.ambient_valid hEventCut hReadZ hZLower
          (hBeforePhysical.trans_eq (hSourceRows.trans hRowZ.symm)))
    · obtain ⟨father, hFather⟩ := nextUCopy.source_parent_some_of_marked hNextUReal hMarked
      have hEq := nextUCopy.actual_common_marker_band_event_depth_eq nextZCopy hLast s.ambient_valid hTargetWidth
        (by simpa only [hNextUColumn, hNextZColumn] using hColumn)
        hFather (hNextCommon.symm.trans hFather) hMarked hNextCut hNextUFront hNextZFront
        (le_of_not_gt hBeforePhysical) hBelowTarget
      simpa only [hUOutputColumn, hZOutputColumn] using hEq
  · have hnu := fun hi => hMarked ((marked_index_iff p nextU).mp hi)
    have hnz := fun hi => hMarked (hMarkedIff.mpr ((marked_index_iff p nextZ).mp hi))
    obtain ⟨upperU, hReadU, hRowU⟩ := uCopy.effective_upper_row_all hLast hUReal nextUCopy hUUpper hnu
    obtain ⟨upperZ, hReadZ, hRowZ⟩ := zCopy.effective_upper_row_all hLast hZReal nextZCopy hZUpper hnz
    exact s.copied_depth_eq_at_frontiers_of_source_cut history hLast hStartRun hUBefore hZBefore
      uCopy zCopy hSourceWidth hTargetWidth hCut hUFront hZFront (hUP.trans hZP.symm)
      (uCopy.frontierAt_of_upper_read s.ambient_valid hEventCut hReadU hULower (hBelowTarget.trans_eq hRowU.symm))
      (zCopy.frontierAt_of_upper_read s.ambient_valid hEventCut hReadZ hZLower
        (hBelowTarget.trans_eq (hOutputRows.trans hRowZ.symm)))

end Actual
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.common_parent_upper_interval_depth_eq
