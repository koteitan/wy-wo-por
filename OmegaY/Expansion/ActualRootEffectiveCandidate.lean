/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualRootEffectiveCandidate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualStationaryEffectiveCandidate

/-!
# Actual nonmarker candidates with a root-column accepted source parent

The candidate and current endpoints remain genuine copied occurrences.
Only the accepted source parent's column bound is relaxed from strictly
right of the root to at or right of it. A rejected source candidate has
an actual upper, so no copied top or frontier is assumed.
-/

namespace OmegaY.Expansion
open Canonical Geometry
theorem Preparation.nonmarker_candidate_of_parent_ge
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {source candidate parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentBound : p.root.column ≤ parent.1.val)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index) :
    candidate.2.val ∉ (p.marked[candidate.1.val]?.getD []).map Ref.index := by
  intro hMarkedIndex
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hCandidateReal := Frame.Q_real hNormal.toOrdered hSourceReal hCandidate
  obtain ⟨marked, hm, hi⟩ := List.mem_map.mp hMarkedIndex
  have hc := (p.marker_iff.mp hm).1
  have hMarkedRef : marked = Frame.ref candidate := by
    cases marked
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨hc, hi⟩
  have hMarked : BucketMem p.marked candidate.1.val (Frame.ref candidate) := hMarkedRef ▸ hm
  obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
    simpa only [hRootRef] using p.markers_built
  obtain ⟨hCandidateRight, low, hLowReal, hLowColumn, hLowIndex, hWhole, hRow⟩ :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hCandidateReal).mp hMarked
  have hCone : Frame.RootCone F low candidate :=
    ⟨candidate, hCandidateReal, rfl, hRow, hWhole⟩
  obtain ⟨_, candidateUpper, _, _, hUpper, hUpperRow⟩ :=
    hCone.successor_at_root hNormal hRow (by simpa only [hLowColumn] using hCandidateRight)
  have hLower : F.height low ≤ F.height source :=
    hRow ▸ Frame.Q_height_le hNormal.toOrdered hCandidate
  have hBefore : F.height source < Row.bump (F.height low) 0 :=
    (Frame.Q_upper_gt hNormal.toOrdered hCandidate hUpper).trans_eq hUpperRow
  have hSourceRow : F.height source = F.height low :=
    (Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero (Row.jump_le_of_lt_bump hLower hBefore))).symm
  obtain ⟨actualCandidate, hActualCandidate, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
  have hCandidateEq : actualCandidate = candidate :=
    Option.some.inj (hActualCandidate.symm.trans hCandidate)
  subst actualCandidate
  have hPath := trace.parentPath hNormal.toOrdered (hNormal.real_positive candidate hCandidateReal)
  have hRootColumn : root.1.val = p.root.column := congrArg Ref.column hRootRef
  have hTail := hPath.suffix_of_column_le hNormal.toOrdered hWhole
    (show low.1.val ≤ parent.1.val by rw [hLowColumn, hRootColumn]; exact hParentBound)
  have hSourceMarked :=
    (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hSourceReal).mpr
      ⟨by rw [hRootColumn]; exact hParentBound.trans_lt (Frame.P_column_lt hNormal.toOrdered hParent),
        low, hLowReal, hLowColumn, hLowIndex, .cons hParent hTail, hSourceRow⟩
  exact hUnmarked (List.mem_map.mpr ⟨Frame.ref source, hSourceMarked, rfl⟩)

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)
theorem stationary_candidate_row_le_of_parent_ge (hLast : 1 < last)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentBound : p.root.column ≤ parent.1.val)
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
    have hCandidateRight := candidateCopy.state.next_lower
    have hSourceRight := copy.state.next_lower
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
        (hRootColumn.trans_le hParentBound)
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
theorem candidate_eq_stationary_of_parent_ge (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentBound : p.root.column ≤ parent.1.val)
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
  have hCandidateRight := candidateCopy.state.next_lower
  have hCandidateUnmarked := p.nonmarker_candidate_of_parent_ge hParent hCandidate hParentBound hUnmarked
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
      exact copy.stationary_candidate_row_le_of_parent_ge hLast candidateCopy hParent hCandidate hParentBound hStationary
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

theorem candidate_eq_raised_of_upper_of_parent_ge (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent candidateUpper : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentBound : p.root.column ≤ parent.1.val)
    (hCandidateUpper : (Frame.ofMountain p.reduced).upper candidate = some candidateUpper)
    (hRaised : (Frame.ofMountain p.reduced).height source < copy.read.outputCell.row) :
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
  have hCandidateReal := Frame.Q_real hNormal.toOrdered hSourceReal hCandidate
  obtain ⟨oldCandidate, hOldCandidate, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
  have hCandidateEq : oldCandidate = candidate := Option.some.inj (hOldCandidate.symm.trans hCandidate)
  subst oldCandidate
  have hPath := trace.parentPath hNormal.toOrdered (hNormal.real_positive candidate hCandidateReal)
  have hCandidateRight := candidateCopy.state.next_lower
  have hSourceRight := copy.state.next_lower
  obtain ⟨index, a, hSourceInside, hCandidateInside⟩ :=
    copy.raised_candidate_interval hLast hUnmarked hCandidate hRaised
  have hSourceRow := copy.interval_row a hSourceInside hSourceRight
  have hCandidateRow := candidateCopy.interval_row a hCandidateInside hCandidateRight
  have hCandidateUnmarked := p.nonmarker_candidate_of_parent_ge hParent hCandidate hParentBound hUnmarked
  obtain ⟨candidateParent, hCandidateParent, _, _, _⟩ :=
    hNormal.upper_step candidate candidateUpper hCandidateReal hCandidateUpper
  have hRootCandidate : (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row ≤
      F.height candidate := by simpa only [a.root_row] using hCandidateInside.2.1
  have hRootSource : (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row ≤
      F.height source := by simpa only [a.root_row] using hSourceInside.2.1
  obtain ⟨upperCell, hUpperRead, hUpperRow⟩ := candidateCopy.upper_read_of_lower_lift
    hLast hCandidateUnmarked hCandidateParent hCandidateUpper hRootCandidate hCandidateRow
  obtain ⟨actualSource, actualCandidate, hActualSourceRef, _, hActualQ, hSearch,
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
      rw [hExpectedCell, hCandidateRow, hSourceRow]
      rcases eq_or_lt_of_le (Frame.Q_height_le hNormal.toOrdered hCandidate) with he | hl
      · exact le_of_eq (congrArg _ he)
      · exact (Row.lift_strictMono hRootCandidate hl).le
    · intro upper hUpper
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
      change copy.read.outputCell.row < (G.cell upper).row
      rw [hSourceRow, hCellEq, hUpperRow]
      exact Row.lift_strictMono hRootSource
        (Frame.Q_upper_gt hNormal.toOrdered hCandidate hCandidateUpper)
  rw [hColumns, hFront] at hExpectedFront
  have hActualRef : Frame.ref actualCandidate = candidateCopy.outputRef :=
    (congrArg Frame.ref hExpectedFront).trans hExpectedRef
  exact ⟨actualSource, actualCandidate, hActualSourceRef, hActualRef, hActualQ,
    by simpa only [hActualRef] using hSearch⟩

/-- The rejected candidate's source upper is supplied by the successful
source search itself. The two actual current-row alternatives are exhaustive. -/
theorem candidate_eq_nondirect_nonmarker_of_parent_ge
    (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentBound : p.root.column ≤ parent.1.val) (hDistinct : candidate ≠ parent) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      Frame.ref actualCandidate = candidateCopy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok candidateCopy.outputRef := by
  rcases eq_or_lt_of_le copy.read.source_row_le_output with hStationary | hRaised
  · exact copy.candidate_eq_stationary_of_parent_ge hLast hValid hUnmarked candidateCopy
      hParent hCandidate hParentBound hStationary.symm
  · have hNormal := build_normal_of_success p.reduced_build
    obtain ⟨blocker, _, _, path, hLastParent, _⟩ :=
      hNormal.source_last_blocker hParent hCandidate hDistinct
    have hHasParent : ∃ candidateParent, (Frame.ofMountain p.reduced).P candidate = some candidateParent := by
      cases path with
      | refl => exact ⟨parent, hLastParent⟩
      | cons hFirst _ => exact ⟨_, hFirst⟩
    obtain ⟨candidateParent, hCandidateParent⟩ := hHasParent
    obtain ⟨upper, hUpper⟩ := hNormal.upper_of_parent hCandidateParent
    exact copy.candidate_eq_raised_of_upper_of_parent_ge hLast hValid hUnmarked candidateCopy
      hParent hCandidate hParentBound hUpper hRaised

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.nonmarker_candidate_of_parent_ge
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.stationary_candidate_row_le_of_parent_ge
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_stationary_of_parent_ge
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_raised_of_upper_of_parent_ge
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_nondirect_nonmarker_of_parent_ge
