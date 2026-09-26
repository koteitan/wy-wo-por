/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualStationaryEffectiveCandidate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowEffectiveCandidate

/-!
# Actual candidate identification when the current occurrence is stationary

The candidate is not assumed stationary. If it rises, its actual reference
interval is transported along the source P-record path up to the source
parent. The current node then lies in that same cone, either inside the
interval or above its cap. Both alternatives bound the actual candidate
below the stationary current row. Actual upper reads supply the other bound.
-/

namespace OmegaY.Geometry.Frame

/-- A real source record path whose endpoint remains at or right of the
root cannot leave the interval through a strict-left root exit. -/
theorem ParentPath.root_interval_of_endpoint_column {F : Frame} (hF : F.Normal)
    {root source endpoint : F.Node} {cap : Row} (hRootReal : Real root)
    (hCap : Row.bump (F.height root) 0 < cap)
    (hBarrier : ∀ upper, F.upper root = some upper → cap ≤ F.height upper)
    (path : ParentPath F source endpoint) (hInside : RootInterval F root cap source)
    (hRight : root.1.val ≤ endpoint.1.val) : RootInterval F root cap endpoint := by
  induction path with
  | refl => exact hInside
  | @cons source next endpoint hNext tail ih =>
    have hNextInside := (root_interval_parent_iff_column hF hRootReal hCap hBarrier
      hNext hInside).mpr (hRight.trans (tail.column_le hF.toOrdered))
    exact ih hNextInside hRight

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- This derives the missing cross-column lower bound from actual data.
The old candidate may have risen even though the current source has not. -/
theorem stationary_candidate_row_le (hLast : 1 < last)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentRight : p.root.column < parent.1.val)
    (hStationary : copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source) :
    candidateCopy.read.outputCell.row ≤ copy.read.outputCell.row := by
  let F := Frame.ofMountain p.reduced
  have hNormal : F.Normal := build_normal_of_success p.reduced_build
  have hCandidateBelow := Frame.Q_height_le hNormal.toOrdered hCandidate
  by_cases hCandidateStationary : candidateCopy.read.outputCell.row = F.height candidate
  · rw [hCandidateStationary, hStationary]
    exact hCandidateBelow
  · have hCandidateRaised : F.height candidate < candidateCopy.read.outputCell.row :=
      lt_of_le_of_ne candidateCopy.read.source_row_le_output (Ne.symm hCandidateStationary)
    let md := candidateCopy.data.marker_data candidateCopy.read.marker candidateCopy.read.marker_mem
    have hRaisedLift : F.height candidate < Row.lift md.current.row md.targetCell.row (F.height candidate) := by
      simpa only [candidateCopy.read.output_row, Frame.height, md, F] using hCandidateRaised
    have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
      ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
    obtain ⟨oldCandidate, hOldCandidate, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
    have he : oldCandidate = candidate := Option.some.inj (hOldCandidate.symm.trans hCandidate)
    subst oldCandidate
    have path := trace.parentPath hNormal.toOrdered
      (hNormal.real_positive candidate (Frame.Q_real hNormal.toOrdered hSourceReal hCandidate))
    have hCandidateRight := hParentRight.trans_le (path.column_le hNormal.toOrdered)
    have hSourceRight := hParentRight.trans (Frame.P_column_lt hNormal.toOrdered hParent)
    rcases candidateCopy.state.marker_source_transport hLast candidateCopy.data
        candidateCopy.read.marker_mem rfl candidateCopy.read.marker_before with
      ⟨_, hFixed⟩ | ⟨index, a, _, hTargetRaised, hInside | ⟨_, hFixed⟩⟩
    · exact False.elim ((ne_of_lt hRaisedLift) hFixed.symm)
    · have hRootRow : F.height a.root = md.current.row := a.root_row
      have hRootColumn : a.root.1.val = p.root.column := congrArg Ref.column a.root_ref
      have hBarrier : ∀ upper, F.upper a.root = some upper →
          Row.bump (F.height a.root) a.degree ≤ F.height upper := by
        simpa only [hRootRow] using a.root_upper_barrier
      have hInside' : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) candidate := by
        rw [hRootRow]
        exact hInside
      have hParentInside := path.root_interval_of_endpoint_column hNormal a.root_real
        (Row.bump_strictMono_exponent _ (a.raised_degree hTargetRaised)) hBarrier hInside'
        (hRootColumn.trans_le hParentRight.le)
      have hCandidateRow := candidateCopy.interval_row a hInside hCandidateRight
      rcases Frame.root_interval_child_or_above_cap hNormal hParent hParentInside with
        hSourceInside | hAboveCap
      · rw [hRootRow] at hSourceInside
        have hSourceRow := copy.interval_row a hSourceInside hSourceRight
        rw [hCandidateRow, hSourceRow]
        have hRootBelow : md.current.row ≤ F.height candidate := by
          simpa only [hRootRow] using hInside'.2.1
        rcases eq_or_lt_of_le hCandidateBelow with he | hl
        · exact le_of_eq (congrArg _ he)
        · exact (Row.lift_strictMono hRootBelow hl).le
      · have hLiftBelow : Row.lift md.current.row a.target.row (F.height candidate) <
            Row.bump md.current.row a.degree :=
          (Row.lift_mem_interval a.target_lower a.target_below
            (by simpa only [hRootRow] using hInside'.2.1) (by simpa only [hRootRow] using hInside'.2.2)).2
        rw [hCandidateRow, hStationary]
        exact hLiftBelow.le.trans (by simpa only [hRootRow] using hAboveCap)
    · exact False.elim ((ne_of_lt hRaisedLift) hFixed.symm)

/-- No stationarity of the candidate is assumed. Its actual upper is never
below its source upper, so the source Q upper barrier remains strict. -/
theorem candidate_eq_stationary (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentRight : p.root.column < parent.1.val)
    (hStationary : copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      Frame.ref actualCandidate = candidateCopy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok candidateCopy.outputRef := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨oldCandidate, hOldCandidate, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
  have he : oldCandidate = candidate := Option.some.inj (hOldCandidate.symm.trans hCandidate)
  subst oldCandidate
  have path := trace.parentPath hNormal.toOrdered
    (hNormal.real_positive candidate (Frame.Q_real hNormal.toOrdered hSourceReal hCandidate))
  have hCandidateRight := hParentRight.trans_le (path.column_le hNormal.toOrdered)
  have hCandidateUnmarked := p.nonmarker_candidate hParent hCandidate hParentRight hUnmarked
  obtain ⟨actualSource, actualCandidate, hSourceRef, _, hActualQ, hSearch,
      hColumn, hCut, hFront⟩ :=
    copy.candidate_frontier hLast hValid hUnmarked hCandidate hCandidateRight.le
  obtain ⟨expected, hExpectedRef, hExpectedCell⟩ :=
    Canonical.frame_node_of_cellAt candidateCopy.output_read
  have hColumns : expected.1 = actualCandidate.1 := Fin.ext
    ((congrArg Ref.column hExpectedRef).trans candidateCopy.source_column |>.trans hColumn.symm)
  have hExpectedFront : Frame.frontierAt hValid.toOrdered copy.read.outputCell.row hCut expected.1 =
      expected := by
    apply Frame.frontierAt_eq_of_upper_barrier hValid.toOrdered hCut
    · change (G.cell expected).row ≤ _
      rw [hExpectedCell]
      exact copy.stationary_candidate_row_le hLast candidateCopy hParent hCandidate hParentRight hStationary
    · intro upper hUpper
      cases hSourceUpper : F.upper candidate with
      | none =>
        rw [candidateCopy.top_upper_none hLast hSourceUpper hExpectedRef] at hUpper
        cases hUpper
      | some sourceUpper =>
        obtain ⟨upperCell, hUpperRead, hUpperRow⟩ :=
          candidateCopy.upper_lift_read hLast hCandidateUnmarked hSourceUpper
        have hSpec := Frame.upper_spec hUpper
        have hColumnRef := congrArg Ref.column hExpectedRef
        have hIndexRef := congrArg Ref.index hExpectedRef
        have hUpperRef : Frame.ref upper =
            ⟨candidateCopy.outputRef.column, candidateCopy.outputRef.index + 1⟩ := by
          simp only [Frame.ref, Ref.mk.injEq]
          exact ⟨(congrArg Fin.val hSpec.1).trans hColumnRef, by
            change expected.2.val = candidateCopy.outputRef.index at hIndexRef
            omega⟩
        have hActualRead := Canonical.cellAt_of_frame_node result upper
        rw [hUpperRef] at hActualRead
        have hCellEq : G.cell upper = upperCell := Except.ok.inj (hActualRead.symm.trans hUpperRead)
        have hBefore := Frame.Q_upper_gt hNormal.toOrdered hCandidate hSourceUpper
        have hRootUpper := candidateCopy.read.source_lower.trans
          ((Frame.Q_height_le hNormal.toOrdered hCandidate).trans hBefore.le)
        have hUpperLift := Row.lift_ge_source
          (candidateCopy.data.marker_data candidateCopy.read.marker candidateCopy.read.marker_mem).target_lower
          hRootUpper
        change copy.read.outputCell.row < (G.cell upper).row
        rw [hStationary, hCellEq, hUpperRow]
        exact hBefore.trans_le hUpperLift
  rw [hColumns, hFront] at hExpectedFront
  have hActualRef : Frame.ref actualCandidate = candidateCopy.outputRef :=
    (congrArg Frame.ref hExpectedFront).trans hExpectedRef
  exact ⟨actualSource, actualCandidate, hSourceRef, hActualRef, hActualQ,
    by simpa only [hActualRef] using hSearch⟩

/-- Complete nonmarker/current and strict-right-source-parent candidate
identification. Both actual row branches are selected internally. -/
theorem candidate_eq_nonmarker (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentRight : p.root.column < parent.1.val) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      Frame.ref actualCandidate = candidateCopy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok candidateCopy.outputRef := by
  rcases eq_or_lt_of_le copy.read.source_row_le_output with hStationary | hRaised
  · exact copy.candidate_eq_stationary hLast hValid hUnmarked candidateCopy
      hParent hCandidate hParentRight hStationary.symm
  · exact copy.candidate_eq_raised hLast hValid hUnmarked candidateCopy
      hParent hCandidate hParentRight hRaised

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.ParentPath.root_interval_of_endpoint_column
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.stationary_candidate_row_le
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_stationary
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_nonmarker
