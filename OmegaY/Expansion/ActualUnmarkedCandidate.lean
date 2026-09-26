/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualUnmarkedCandidate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.RootCandidateCone
import OmegaY.Expansion.ActualRootEffectiveCandidate

/-!
# Actual candidate identification when both source endpoints are unmarked

The accepted source parent may lie in the good part. An actually raised
candidate controls a real root interval. Above the root row, its Q cone
pulls back to the current source column; at or above the cap, its lifted
row is already below the current source. This proves the missing lower
bound without requiring the accepted parent to remain inside the interval.
-/

namespace OmegaY.Expansion
open Canonical Geometry

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

theorem stationary_unmarked_candidate_row_le (hLast : 1 < last)
    {candidate : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hCandidateUnmarked : candidate.2.val ∉ (p.marked[candidate.1.val]?.getD []).map Ref.index)
    (hStationary : copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source) :
    candidateCopy.read.outputCell.row ≤ copy.read.outputCell.row := by
  let F := Frame.ofMountain p.reduced
  let md := candidateCopy.data.marker_data candidateCopy.read.marker candidateCopy.read.marker_mem
  have hNormal := build_normal_of_success p.reduced_build
  have hQHeight := Frame.Q_height_le hNormal.toOrdered hCandidate
  by_cases hCandidateFixed : candidateCopy.read.outputCell.row = F.height candidate
  · rw [hCandidateFixed, hStationary]
    exact hQHeight
  · have hRaised : F.height candidate < Row.lift md.current.row md.targetCell.row (F.height candidate) := by
      have hStrict := lt_of_le_of_ne candidateCopy.read.source_row_le_output (Ne.symm hCandidateFixed)
      simpa only [candidateCopy.read.output_row, Frame.height, md, F] using hStrict
    have hAfter : candidateCopy.read.marker.index < candidate.2.val := by
      have hBefore := candidateCopy.read.marker_before
      have hNe : candidateCopy.read.marker.index ≠ candidate.2.val := by
        intro he
        exact hCandidateUnmarked (he ▸ List.mem_map.mpr
          ⟨candidateCopy.read.marker, candidateCopy.read.marker_mem, rfl⟩)
      omega
    have hRootBelow : md.current.row < F.height candidate :=
      candidateCopy.data.source_valid.rows_strict _ _ _ _ md.current_at candidateCopy.read.source_at hAfter
    rcases candidateCopy.state.marker_source_transport hLast candidateCopy.data
        candidateCopy.read.marker_mem rfl candidateCopy.read.marker_before with
      ⟨_, hFixed⟩ | ⟨index, a, _, _, hInside | ⟨_, hFixed⟩⟩
    · exact ((ne_of_lt hRaised) hFixed.symm).elim
    · have hCandidateRow := candidateCopy.interval_row a hInside candidateCopy.state.next_lower
      by_cases hBelow : F.height source < Row.bump md.current.row a.degree
      · have hRootAbove : F.height a.root < F.height source :=
          a.root_row.trans_lt (hRootBelow.trans_le hQHeight)
        have hSourceCone := Frame.root_cone_child_of_candidate hNormal a.root_real hCandidate
          hInside.1 hRootAbove (by simpa only [a.root_row] using hInside.2.1)
        have hSourceInside : Frame.RootInterval F a.root (Row.bump md.current.row a.degree) source :=
          ⟨hSourceCone, hRootAbove.le, hBelow⟩
        have hSourceRow := copy.interval_row a hSourceInside copy.state.next_lower
        rw [hCandidateRow, hSourceRow]
        rcases eq_or_lt_of_le hQHeight with he | hl
        · exact le_of_eq (congrArg _ he)
        · exact (Row.lift_strictMono hRootBelow.le hl).le
      · have hLiftBelow := (Row.lift_mem_interval a.target_lower a.target_below
          (by simpa only [a.root_row] using hInside.2.1)
          (by simpa only [a.root_row] using hInside.2.2)).2
        rw [hCandidateRow, hStationary]
        exact hLiftBelow.le.trans (le_of_not_gt hBelow)
    · exact ((ne_of_lt hRaised) hFixed.symm).elim

theorem candidate_eq_stationary_of_unmarked_candidate (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hCandidateUnmarked : candidate.2.val ∉ (p.marked[candidate.1.val]?.getD []).map Ref.index)
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
      exact copy.stationary_unmarked_candidate_row_le hLast candidateCopy hCandidate hCandidateUnmarked hStationary
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

theorem candidate_eq_raised_of_upper_of_unmarked_candidate (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent candidateUpper : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hCandidateUnmarked : candidate.2.val ∉ (p.marked[candidate.1.val]?.getD []).map Ref.index)
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
theorem candidate_eq_nondirect_of_unmarked_pair
    (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hCandidateUnmarked : candidate.2.val ∉ (p.marked[candidate.1.val]?.getD []).map Ref.index) (hDistinct : candidate ≠ parent) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      Frame.ref actualCandidate = candidateCopy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok candidateCopy.outputRef := by
  rcases eq_or_lt_of_le copy.read.source_row_le_output with hStationary | hRaised
  · exact copy.candidate_eq_stationary_of_unmarked_candidate hLast hValid hUnmarked candidateCopy
      hParent hCandidate hCandidateUnmarked hStationary.symm
  · have hNormal := build_normal_of_success p.reduced_build
    obtain ⟨blocker, _, _, path, hLastParent, _⟩ :=
      hNormal.source_last_blocker hParent hCandidate hDistinct
    have hHasParent : ∃ candidateParent, (Frame.ofMountain p.reduced).P candidate = some candidateParent := by
      cases path with
      | refl => exact ⟨parent, hLastParent⟩
      | cons hFirst _ => exact ⟨_, hFirst⟩
    obtain ⟨candidateParent, hCandidateParent⟩ := hHasParent
    obtain ⟨upper, hUpper⟩ := hNormal.upper_of_parent hCandidateParent
    exact copy.candidate_eq_raised_of_upper_of_unmarked_candidate hLast hValid hUnmarked candidateCopy
      hParent hCandidate hCandidateUnmarked hUpper hRaised

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.stationary_unmarked_candidate_row_le

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_stationary_of_unmarked_candidate
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_raised_of_upper_of_unmarked_candidate
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_nondirect_of_unmarked_pair

