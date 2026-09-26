/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualAnyHighCandidate.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualStationaryMarkerCandidate
import OmegaY.Expansion.ActualHighFrontierCopy
import OmegaY.Expansion.ActualHighRootValue

/-! High actual Q candidates, including preserved good columns and the
changing block-start boundary. These results identify the actual initial
candidate only; they do not assert numerical parent recognition. -/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {source : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  (copy : EffectiveCopyOccurrence p block start references source result)

/-- The real own-cell copy puts Q in the fixed source column or its
shifted column, according to the executable copyEdge branch. -/
theorem candidate_frontier_all_columns (hValid : MountainValid result)
    (hReal : Frame.Real source) {copied : Cell}
    (hCopy : copyEdge copy.before (Frame.ref source) (block * (p.reduced.size - 1 - p.root.column))
      p.root.column copy.read.outputCell.row = .ok copied)
    (hShape : SameShape copied copy.read.outputCell)
    {candidate : (Frame.ofMountain p.reduced).Node}
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      (Frame.ofMountain result).cell actualSource = copy.read.outputCell ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok (Frame.ref actualCandidate) ∧
      actualCandidate.1.val = (if candidate.1.val < p.root.column then candidate.1.val else
        candidate.1.val + block * (p.reduced.size - 1 - p.root.column)) ∧
      ∃ hCut : (1 : Row) ≤ copy.read.outputCell.row,
        Frame.frontierAt hValid.toOrdered copy.read.outputCell.row hCut actualCandidate.1 =
          actualCandidate := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceRead : lookup copy.before (Frame.ref source) = .ok (F.cell source) :=
    lookup_ok_iff.mpr ⟨copy.data.sources, copy.data.source_column, copy.read.source_at⟩
  have hPositive : (0 : Row) < (F.cell source).row :=
    Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hReal)
  obtain ⟨expected, parentRef, parentCell, hExpected, _, _, hExpectedLeft,
      hParentRead, hParentColumn, oldParent, hOldLeft, _, hEndpoint⟩ :=
    copyEdge_nonphantom_total copy.data.ambient_valid hSourceRead copy.data.source_nonzero
      copy.data.destination.le (ne_of_gt hPositive)
      (hPositive.trans_le copy.read.source_row_le_output)
  have hExpectedEq : expected = copied := Except.ok.inj (hExpected.symm.trans hCopy)
  subst expected
  obtain ⟨oldLeft, hLeft, _, _, hCandidateColumn, _⟩ :=
    Frame.Q_spec hNormal.toOrdered hCandidate
  have hOldParent : oldParent = Frame.ref oldLeft :=
    Option.some.inj (hOldLeft.symm.trans hLeft)
  have hOldColumn : oldParent.column = candidate.1.val := by
    rw [hOldParent]
    exact (congrArg Fin.val hCandidateColumn).symm
  have hSelectedColumn : parentRef.column =
      (if candidate.1.val < p.root.column then candidate.1.val else
        candidate.1.val + block * (p.reduced.size - 1 - p.root.column)) := by
    rcases hEndpoint with ⟨hFixed, hRef, _⟩ | ⟨hMoved, hColumn, _, _⟩
    · have hlt : candidate.1.val < p.root.column := hOldColumn ▸ hFixed
      simp only [if_pos hlt]
      exact (congrArg Ref.column hRef).trans hOldColumn
    · have hle : p.root.column ≤ candidate.1.val := hOldColumn ▸ hMoved
      simp only [if_neg (not_lt_of_ge hle)]
      exact hColumn.trans (congrArg (fun n => n + block *
        (p.reduced.size - 1 - p.root.column)) hOldColumn)
  have hParentBound : parentRef.column < copy.before.size :=
    copy.data.destination ▸ hParentColumn
  have hParentResult : Canonical.cellAt result parentRef = .ok parentCell :=
    (copy.preserved.cellAt (by simpa using Nat.lt_succ_of_lt hParentBound)).trans
      (((PreservesColumns.push copy.before copy.column).cellAt hParentBound).trans
      (cellAt_ok_iff.mpr (lookup_ok_iff.mp hParentRead)))
  obtain ⟨actualParent, hActualParentRef, _⟩ := Canonical.frame_node_of_cellAt hParentResult
  obtain ⟨actualSource, hActualSourceRef, hActualSourceCell⟩ :=
    Canonical.frame_node_of_cellAt copy.output_read
  have hActualLeft : (G.cell actualSource).left = some (Frame.ref actualParent) := by
    rw [hActualSourceCell, hActualParentRef]
    exact hShape.2.symm.trans hExpectedLeft
  obtain ⟨actualCandidate, hActualCandidate, hSearch⟩ :=
    Executable.candidate_of_stored hValid.toOrdered hActualLeft
  obtain ⟨selected, hSelected, _, _, hActualColumn, _⟩ :=
    Frame.Q_spec hValid.toOrdered hActualCandidate
  have hSelectedEq : selected = actualParent := Executable.ref_injective G
    (Option.some.inj (hSelected.symm.trans hActualLeft))
  subst selected
  have hActualReal : Frame.Real actualSource := by
    have hIndex := congrArg Ref.index hActualSourceRef
    change actualSource.2.val = copy.read.outputIndex at hIndex
    change 0 < actualSource.2.val
    rw [hIndex]
    exact copy.read.output_real hReal
  have hCut : (1 : Row) ≤ copy.read.outputCell.row := by
    rw [← hActualSourceCell]
    exact Frame.one_le_height hValid.toOrdered hActualReal
  refine ⟨actualSource, actualCandidate, hActualSourceRef, hActualSourceCell,
    hActualCandidate, ?_, ?_, hCut, ?_⟩
  · simpa only [hActualSourceRef] using hSearch
  · exact (congrArg Fin.val hActualColumn).trans
      ((congrArg Ref.column hActualParentRef).trans hSelectedColumn)
  · apply Frame.frontierAt_eq_of_upper_barrier hValid.toOrdered hCut
    · simpa only [Frame.height, hActualSourceCell] using
        Frame.Q_height_le hValid.toOrdered hActualCandidate
    · intro upper hUpper
      simpa only [Frame.height, hActualSourceCell] using
        Frame.Q_upper_gt hValid.toOrdered hActualCandidate hUpper

end EffectiveCopyOccurrence

/-- Three actual sources for a high candidate. The root case records the
real block-start frontier and its preserved full cell, together with the
proved numerical equality to the old root-column candidate. -/
def HighCandidateOrigin {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (candidate : (Frame.ofMountain p.reduced).Node) (cut : Row) (hOne : (1 : Row) ≤ cut)
    (actual : (Frame.ofMountain ambient).Node) : Prop :=
  (candidate.1.val < p.root.column ∧ Frame.ref actual = Frame.ref candidate ∧
    (Frame.ofMountain ambient).cell actual = (Frame.ofMountain p.reduced).cell candidate) ∨
  (candidate.1.val = p.root.column ∧
    ∃ boundary : (Frame.ofMountain start).Node,
      boundary.1.val = start.size - 1 ∧
      frontierAt s.start_valid.toOrdered cut hOne boundary.1 = boundary ∧
      Frame.ref actual = Frame.ref boundary ∧
      (Frame.ofMountain ambient).cell actual = (Frame.ofMountain start).cell boundary ∧
      (Frame.ofMountain ambient).value actual = (Frame.ofMountain p.reduced).value candidate) ∨
  (p.root.column < candidate.1.val ∧
    ∃ copied : EffectiveCopyOccurrence p block start references candidate ambient,
      Frame.ref actual = copied.outputRef ∧
      (Frame.ofMountain ambient).cell actual = copied.read.outputCell)

/-- Every actual high copied node with an old Q has a real new Q of one
of the three stated origins. Source Q may lie below the high threshold.
No numerical P equation for the copied graph is an input or a conclusion. -/
theorem DynamicBlockState.actual_any_high_candidate
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next startCopies : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    {source candidate : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source ambient)
    (hSourceBefore : source.1.val < next) (hReal : Real source)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate) :
    ∃ actualSource actualCandidate : (Frame.ofMountain ambient).Node,
      Frame.ref actualSource = copy.outputRef ∧
      (Frame.ofMountain ambient).cell actualSource = copy.read.outputCell ∧
      (Frame.ofMountain ambient).Q actualSource = some actualCandidate ∧
      nextCandidate ambient copy.outputRef = .ok (Frame.ref actualCandidate) ∧
      ∃ hOne : (1 : Row) ≤ (Frame.ofMountain p.reduced).height source,
        frontierAt s.ambient_valid.toOrdered ((Frame.ofMountain p.reduced).height source)
          hOne actualCandidate.1 = actualCandidate ∧
        HighCandidateOrigin s candidate ((Frame.ofMountain p.reduced).height source)
          hOne actualCandidate := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain ambient
  have hNormal := build_normal_of_success p.reduced_build
  have hOne : (1 : Row) ≤ F.height source := Frame.one_le_height hNormal.toOrdered hReal
  have hQReal := Frame.Q_real hNormal.toOrdered hReal hCandidate
  have hQBelow := Frame.Q_height_le hNormal.toOrdered hCandidate
  have hQBarrier : ∀ upper, F.upper candidate = some upper →
      F.height source < F.height upper :=
    fun _ hUpper => Frame.Q_upper_gt hNormal.toOrdered hCandidate hUpper
  have hQFront : frontierAt hNormal.toOrdered (F.height source) hOne candidate.1 = candidate :=
    frontierAt_eq_of_upper_barrier hNormal.toOrdered hOne hQBelow hQBarrier
  have hUnmarked := copy.state.high_source_not_marked hLast source.1.isLt
    copy.data copy.read.source_at hHigh
  have hNoPremature := (copy.state.column_data_parent_inputs hLast source.1.isLt copy.data).1
  obtain ⟨copied, hCopy, hShape⟩ := copy.read.nonmarker_copy_execution hNoPremature hUnmarked
  obtain ⟨actualSource, actualCandidate, hSourceRef, hSourceCell, hActualQ, hSearch,
      hColumn, hCut, hFrontier⟩ :=
    copy.candidate_frontier_all_columns s.ambient_valid hReal hCopy hShape hCandidate
  have hSourceRow := copy.high_row hLast hHigh
  have hFront : frontierAt s.ambient_valid.toOrdered (F.height source) hOne
      actualCandidate.1 = actualCandidate := by
    simpa only [hSourceRow] using hFrontier
  refine ⟨actualSource, actualCandidate, hSourceRef, hSourceCell, hActualQ, hSearch,
    hOne, hFront, ?_⟩
  by_cases hFixed : candidate.1.val < p.root.column
  · have hc : actualCandidate.1.val = candidate.1.val := by simpa only [if_pos hFixed] using hColumn
    let expected := s.base_ambient.mapNode candidate
    have hExpectedFront : frontierAt s.ambient_valid.toOrdered (F.height source) hOne
        expected.1 = expected :=
      frontierAt_of_same_column hNormal.toOrdered s.ambient_valid.toOrdered hOne hQFront
        (s.base_ambient.mapNode_ref candidate) (s.base_ambient _ candidate.1.isLt)
    have hecol : expected.1 = actualCandidate.1 := Fin.ext
      ((s.base_ambient.mapNode_column candidate).trans hc.symm)
    have he : actualCandidate = expected := by rw [hecol, hFront] at hExpectedFront; exact hExpectedFront
    exact Or.inl ⟨hFixed, he ▸ s.base_ambient.mapNode_ref candidate,
      he ▸ s.base_ambient.mapNode_cell candidate⟩
  · have hMoved : p.root.column ≤ candidate.1.val := Nat.le_of_not_gt hFixed
    have hc : actualCandidate.1.val = candidate.1.val +
        block * (p.reduced.size - 1 - p.root.column) := by
      simpa only [if_neg hFixed] using hColumn
    by_cases hRoot : candidate.1.val = p.root.column
    · obtain ⟨_, boundary, hBoundaryColumn, _, hBoundaryFront, _, _, _⟩ :=
        p.blocks_reduced_root_frontier_correspondence hLast hStartRun hOne hHigh hRoot hQFront
      have hBoundaryValue := p.blocks_root_value_at_frontiers hLast hStartRun
        s.start_valid hOne hHigh hRoot hQFront hBoundaryColumn hBoundaryFront
      let expected := s.start_preserved.mapNode boundary
      have hExpectedFront : frontierAt s.ambient_valid.toOrdered (F.height source) hOne
          expected.1 = expected :=
        frontierAt_of_same_column s.start_valid.toOrdered s.ambient_valid.toOrdered hOne
          hBoundaryFront (s.start_preserved.mapNode_ref boundary)
          (s.start_preserved _ boundary.1.isLt)
      have hecol : expected.1 = actualCandidate.1 := by
        apply Fin.ext
        have hMap := s.start_preserved.mapNode_column boundary
        have hSize := s.start_size
        change expected.1.val = _ at hMap ⊢
        omega
      have he : actualCandidate = expected := by rw [hecol, hFront] at hExpectedFront; exact hExpectedFront
      apply Or.inr ∘ Or.inl
      refine ⟨hRoot, boundary, hBoundaryColumn, hBoundaryFront,
        he ▸ s.start_preserved.mapNode_ref boundary,
        he ▸ s.start_preserved.mapNode_cell boundary, ?_⟩
      exact (congrArg Cell.value (he ▸ s.start_preserved.mapNode_cell boundary)).trans hBoundaryValue
    · have hRight : p.root.column < candidate.1.val := lt_of_le_of_ne hMoved (Ne.symm hRoot)
      have hBefore : candidate.1.val < next :=
        (Frame.Q_column_lt hNormal.toOrdered hCandidate).trans hSourceBefore
      obtain ⟨candidateCopy⟩ := s.prior_effective_occurrence history hLast hRight hBefore
      obtain ⟨expected, hExpectedRef, hExpectedCell, hExpectedFront⟩ :=
        candidateCopy.frontierAt_high_of_bounds hLast s.ambient_valid hOne hHigh hQReal hQBelow hQBarrier
      have hecol : expected.1 = actualCandidate.1 := Fin.ext
        (((congrArg Ref.column hExpectedRef).trans candidateCopy.source_column).trans hc.symm)
      have he : actualCandidate = expected := by rw [hecol, hFront] at hExpectedFront; exact hExpectedFront
      exact Or.inr (Or.inr ⟨hRight, candidateCopy, he ▸ hExpectedRef, he ▸ hExpectedCell⟩)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_frontier_all_columns
#print axioms OmegaY.Expansion.DynamicBlockState.actual_any_high_candidate
