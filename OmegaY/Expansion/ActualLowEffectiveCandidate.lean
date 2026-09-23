/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowEffectiveCandidate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveCandidate
import OmegaY.Expansion.ActualCommonParentUpper
import OmegaY.Expansion.SourceLastBlocker
import OmegaY.Expansion.CopiedParentTop

/-!
# Actual candidates of raised nonmarker occurrences

An above-root source's genuine predecessor identifies its Q candidate inside
the same root interval. Thus the real effective copies use a common lift,
rather than assuming cross-column copied frontier compatibility.
-/

namespace OmegaY.Geometry.Frame

/-- The current source node is strictly above the root row. Its preceding
source edge remains inside the interval, and actual Q either stays at its
parent or advances to that parent's equal-height upper. -/
theorem root_interval_candidate_of_above_root {F : Frame} (hF : F.Normal)
    {root source candidate : F.Node} {cap : Row} (hRootReal : Real root)
    (hCap : Row.bump (F.height root) 0 < cap)
    (hBarrier : ∀ upper, F.upper root = some upper → cap ≤ F.height upper)
    (hInside : RootInterval F root cap source) (hAbove : F.height root < F.height source)
    (hCandidate : F.Q source = some candidate) : RootInterval F root cap candidate := by
  obtain ⟨lower, hLowerReal, hUpper, hColumn, _⟩ := real_lower_of_height_lt hF.toOrdered hRootReal hAbove
  obtain ⟨low, hLowReal, hLowColumn, hLowRow, hPath⟩ := hInside.1
  have hRootLower : F.height root ≤ F.height lower := by
    rw [← hLowRow]
    exact height_le_lower_of_lt_upper hF.toOrdered hUpper hLowColumn (hLowRow ▸ hAbove)
  have hLowerSource : F.height lower < F.height source := by
    obtain ⟨parent, _, hRow, _, _⟩ := hF.upper_step lower source hLowerReal hUpper
    rw [hRow]
    exact Row.lt_B _ _
  have hLowerInside : RootInterval F root cap lower :=
    ⟨⟨low, hLowReal, hLowColumn.trans hColumn.symm, hLowRow, hPath⟩,
      hRootLower, hLowerSource.trans hInside.2.2⟩
  obtain ⟨oldParent, hParent, _, _, _⟩ := hF.upper_step lower source hLowerReal hUpper
  have hParentInside := root_interval_internal_parent hF hRootReal hCap hBarrier
    hParent hLowerInside hUpper hInside.2.2
  rcases candidate_after_upper hF hParent hUpper with hSame | ⟨next, hNext, hNextRow, hSame⟩
  · have hEq : candidate = oldParent := Option.some.inj (hCandidate.symm.trans hSame)
    exact hEq ▸ hParentInside
  · have hEq : candidate = next := Option.some.inj (hCandidate.symm.trans hSame)
    subst candidate
    exact ⟨hParentInside.1.same_column (upper_spec hNext).1.symm,
      hNextRow ▸ hInside.2.1, hNextRow ▸ hInside.2.2⟩

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- Both interval memberships come from the current occurrence's actual
marker/reference execution and the source Q operation. -/
theorem raised_candidate_interval (hLast : 1 < last)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate : (Frame.ofMountain p.reduced).Node}
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hRaised : (Frame.ofMountain p.reduced).height source < copy.read.outputCell.row) :
    ∃ rootIndex, ∃ a : ActualRootInterval p start copy.before references rootIndex
        (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row,
      Frame.RootInterval (Frame.ofMountain p.reduced) a.root
        (Row.bump (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row a.degree) source ∧
      Frame.RootInterval (Frame.ofMountain p.reduced) a.root
        (Row.bump (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row a.degree) candidate := by
  let F := Frame.ofMountain p.reduced
  let md := copy.data.marker_data copy.read.marker copy.read.marker_mem
  have hRaisedLift : F.height source < Row.lift md.current.row md.targetCell.row (F.height source) := by
    simpa only [copy.read.output_row, Frame.height, md, F] using hRaised
  have hAfter : copy.read.marker.index < source.2.val := by
    apply lt_of_le_of_ne copy.read.marker_before
    intro he
    exact hUnmarked (he ▸ List.mem_map.mpr ⟨copy.read.marker, copy.read.marker_mem, rfl⟩)
  have hAbove : md.current.row < F.height source :=
    copy.data.source_valid.rows_strict _ _ _ _ md.current_at copy.read.source_at hAfter
  rcases copy.state.marker_source_transport hLast copy.data copy.read.marker_mem rfl copy.read.marker_before with
    ⟨_, hFixed⟩ | ⟨index, a, _, hTargetRaised, hInside | ⟨_, hFixed⟩⟩
  · exact False.elim ((ne_of_lt hRaisedLift) hFixed.symm)
  · have hRootRow : F.height a.root = md.current.row := a.root_row
    have hBarrier : ∀ upper, F.upper a.root = some upper →
        Row.bump (F.height a.root) a.degree ≤ F.height upper := by
      simpa only [hRootRow] using a.root_upper_barrier
    have hSourceInside' : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) source := by
      rw [hRootRow]
      exact hInside
    have hAbove' : F.height a.root < F.height source := by rw [hRootRow]; exact hAbove
    have hCandidateInside : Frame.RootInterval F a.root (Row.bump (F.height a.root) a.degree) candidate :=
      Frame.root_interval_candidate_of_above_root
      (build_normal_of_success p.reduced_build) a.root_real
      (Row.bump_strictMono_exponent _ (a.raised_degree hTargetRaised)) hBarrier
      hSourceInside' hAbove' hCandidate
    rw [hRootRow] at hCandidateInside
    exact ⟨index, a, hInside, hCandidateInside⟩
  · exact False.elim ((ne_of_lt hRaisedLift) hFixed.symm)

/-- A source top's actual effective occurrence is the returned column top.
The maximal controlling marker follows from the source read's maximality. -/
theorem top_output_index (hLast : 1 < last)
    (hTop : (Frame.ofMountain p.reduced).upper source = none) :
    copy.read.outputIndex = copy.column.size - 1 := by
  let F := Frame.ofMountain p.reduced
  let d := copy.data
  have hSources : p.reduced[source.1.val]? = some d.sources :=
    (copy.state.base_ambient source.1.val source.1.isLt).symm.trans d.source_column
  have hLength : F.length source.1 = d.sources.size :=
    congrArg Array.size (Array.getElem?_eq_some_iff.mp hSources).2
  have hNotUpper : ¬ source.2.val + 1 < F.length source.1 := by
    intro h
    change F.upper source = none at hTop
    simp only [Frame.upper, h, ↓reduceDIte] at hTop
    cases hTop
  have hSourceIndex : source.2.val = d.sources.size - 1 := by
    have hBound := source.2.isLt
    change source.2.val < F.length source.1 at hBound
    omega
  have hHighest : ∀ other ∈ d.bucket, other.index ≤ copy.read.marker.index := by
    intro other hm
    by_contra hNot
    have hBefore := (d.marker_before_source_top hm).le
    rw [← hSourceIndex] at hBefore
    exact copy.read.no_between other.index (Nat.lt_of_not_ge hNot) hBefore
      (List.mem_map.mpr ⟨other, hm, rfl⟩)
  obtain ⟨hNoPremature, hParentPower, hParentLow⟩ :=
    copy.state.column_data_parent_inputs hLast source.1.isLt d
  obtain ⟨top, hTopRead, hTopRow, _⟩ := d.copyColumn_lifted_source_top
    hParentPower hParentLow hNoPremature copy.read.copy_run copy.read.marker_mem hHighest
    (by simpa only [hSourceIndex] using copy.read.source_at)
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have hEq : actual = copy.column := Except.ok.inj (hActual.symm.trans copy.read.copy_run)
  subst actual
  exact column_read_index_eq_of_row hValid copy.read.output_at hTopRead
    (copy.read.output_row.trans hTopRow.symm)

/-- Complete-column preservation excludes an added upper even after more
columns or blocks have been appended to the queried mountain. -/
theorem top_upper_none (hLast : 1 < last)
    (hTop : (Frame.ofMountain p.reduced).upper source = none)
    {actual : (Frame.ofMountain result).Node} (hRef : Frame.ref actual = copy.outputRef) :
    (Frame.ofMountain result).upper actual = none := by
  have hIndex := congrArg Ref.index hRef
  change actual.2.val = copy.read.outputIndex at hIndex
  have hColumn := congrArg Ref.column hRef
  change actual.1.val = copy.before.size at hColumn
  have hColumnRead : result[actual.1.val]? = some copy.column := by
    rw [hColumn]
    exact copy.preserved.column_read (by simp)
  have hLength : (Frame.ofMountain result).length actual.1 = copy.column.size :=
    congrArg Array.size (Array.getElem?_eq_some_iff.mp hColumnRead).2
  have hOutputIndex := copy.top_output_index hLast hTop
  have hNot : ¬ actual.2.val + 1 < (Frame.ofMountain result).length actual.1 := by
    rw [hIndex, hOutputIndex, hLength]
    omega
  simp only [Frame.upper, hNot, ↓reduceDIte]

/-- For a genuinely raised current nonmarker, a nontop source candidate
is the actual new candidate. The common lift and its upper barrier are
derived, rather than supplied as cross-column output assumptions. -/
theorem candidate_eq_raised_of_upper (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent candidateUpper : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentRight : p.root.column < parent.1.val)
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
  have hCandidateRight := hParentRight.trans_le (hPath.column_le hNormal.toOrdered)
  have hSourceRight := hParentRight.trans (Frame.P_column_lt hNormal.toOrdered hParent)
  obtain ⟨index, a, hSourceInside, hCandidateInside⟩ :=
    copy.raised_candidate_interval hLast hUnmarked hCandidate hRaised
  have hSourceRow := copy.interval_row a hSourceInside hSourceRight
  have hCandidateRow := candidateCopy.interval_row a hCandidateInside hCandidateRight
  have hCandidateUnmarked := p.nonmarker_candidate hParent hCandidate hParentRight hUnmarked
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

/-- A rejected first candidate has a real subsequent P edge, so its upper
existence is derived from the original successful search, not assumed. -/
theorem candidate_eq_raised_nontrivial (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentRight : p.root.column < parent.1.val) (hDistinct : candidate ≠ parent)
    (hRaised : (Frame.ofMountain p.reduced).height source < copy.read.outputCell.row) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      Frame.ref actualCandidate = candidateCopy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok candidateCopy.outputRef := by
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨blocker, _, _, path, hLastParent, _⟩ :=
    hNormal.source_last_blocker hParent hCandidate hDistinct
  have hHasParent : ∃ candidateParent, (Frame.ofMountain p.reduced).P candidate = some candidateParent := by
    cases path with
    | refl => exact ⟨parent, hLastParent⟩
    | cons hFirst _ => exact ⟨_, hFirst⟩
  obtain ⟨candidateParent, hCandidateParent⟩ := hHasParent
  obtain ⟨upper, hUpper⟩ := hNormal.upper_of_parent hCandidateParent
  exact copy.candidate_eq_raised_of_upper hLast hValid hUnmarked candidateCopy hParent hCandidate
    hParentRight hUpper hRaised

/-- Complete raised-current branch, including a source-top first candidate.
Only actual source P/Q and copy/history data are used. Neither common copied
row inequalities nor a desired target frontier is a premise. -/
theorem candidate_eq_raised (hLast : 1 < last) (hValid : MountainValid result)
    (hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index)
    {candidate parent : (Frame.ofMountain p.reduced).Node}
    (candidateCopy : EffectiveCopyOccurrence p block start references candidate result)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hParentRight : p.root.column < parent.1.val)
    (hRaised : (Frame.ofMountain p.reduced).height source < copy.read.outputCell.row) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      Frame.ref actualCandidate = candidateCopy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok candidateCopy.outputRef := by
  cases hUpper : (Frame.ofMountain p.reduced).upper candidate with
  | some upper =>
    exact copy.candidate_eq_raised_of_upper hLast hValid hUnmarked candidateCopy
      hParent hCandidate hParentRight hUpper hRaised
  | none =>
    have hNormal := build_normal_of_success p.reduced_build
    have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
      ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
    obtain ⟨oldCandidate, hOldCandidate, trace⟩ := (Frame.P_iff hNormal.toOrdered).mp hParent
    have he : oldCandidate = candidate := Option.some.inj (hOldCandidate.symm.trans hCandidate)
    subst oldCandidate
    have path := trace.parentPath hNormal.toOrdered
      (hNormal.real_positive candidate (Frame.Q_real hNormal.toOrdered hSourceReal hCandidate))
    have hCandidateRight := hParentRight.trans_le (path.column_le hNormal.toOrdered)
    have hSourceRight := hParentRight.trans (Frame.P_column_lt hNormal.toOrdered hParent)
    obtain ⟨index, a, hSourceInside, hCandidateInside⟩ :=
      copy.raised_candidate_interval hLast hUnmarked hCandidate hRaised
    have hSourceRow := copy.interval_row a hSourceInside hSourceRight
    have hCandidateRow := candidateCopy.interval_row a hCandidateInside hCandidateRight
    have hRootCandidate : (copy.data.marker_data copy.read.marker copy.read.marker_mem).current.row ≤
        (Frame.ofMountain p.reduced).height candidate := by
      simpa only [a.root_row] using hCandidateInside.2.1
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
      · change ((Frame.ofMountain result).cell expected).row ≤ _
        rw [hExpectedCell, hCandidateRow, hSourceRow]
        rcases eq_or_lt_of_le (Frame.Q_height_le hNormal.toOrdered hCandidate) with he | hl
        · exact le_of_eq (congrArg _ he)
        · exact (Row.lift_strictMono hRootCandidate hl).le
      · intro upper hSome
        rw [candidateCopy.top_upper_none hLast hUpper hExpectedRef] at hSome
        cases hSome
    rw [hColumns, hFront] at hExpectedFront
    have hActualRef : Frame.ref actualCandidate = candidateCopy.outputRef :=
      (congrArg Frame.ref hExpectedFront).trans hExpectedRef
    exact ⟨actualSource, actualCandidate, hSourceRef, hActualRef, hActualQ,
      by simpa only [hActualRef] using hSearch⟩

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.root_interval_candidate_of_above_root
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.raised_candidate_interval
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_raised_of_upper
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_raised_nontrivial
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.top_output_index
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.top_upper_none
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_raised
