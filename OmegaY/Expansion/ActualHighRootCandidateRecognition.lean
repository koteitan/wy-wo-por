/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighRootCandidateRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighFixedCandidateRecognition

/-!
# Actual high root candidates and their numerical record replacement

At a high source cut, a first Q in the root column becomes the true
block-start last-column frontier. Its value equals the source candidate's
value, and each actual source P from that root frontier becomes a genuine
raw edge to the unchanged source parent. The boundary is not identified
with the old root node or assumed to lie on a target numerical path.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem root_candidate_path_first {F : Frame} {q z : F.Node}
    (path : ParentPath F q z) (hNe : q ≠ z) :
    ∃ next, F.P q = some next ∧ ParentPath F next z := by
  cases path with
  | refl _ => exact False.elim (hNe rfl)
  | cons hParent rest => exact ⟨_, hParent, rest⟩

/-- The actual boundary candidate has the source root-frontier value and
the source frontier's outgoing fixed-parent edge. All these facts come
from the real starting-block run and own-cell copy execution. -/
theorem EffectiveCopyOccurrence.candidate_high_root_records
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block startCopies : Nat} {start result : Mountain} {references : List Ref}
    {source candidate : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last) (hValid : MountainValid result)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hReal : Real source)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hRoot : candidate.1.val = p.root.column) :
    ∃ actualSource actualCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      (Frame.ofMountain result).cell actualSource = copy.read.outputCell ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      nextCandidate result copy.outputRef = .ok (Frame.ref actualCandidate) ∧
      (Frame.ofMountain result).value actualCandidate = (Frame.ofMountain p.reduced).value candidate ∧
      (∀ parent, (Frame.ofMountain p.reduced).P candidate = some parent →
        parent.1.val < p.root.column ∧
        RawRefEdge result (Frame.ref actualCandidate) (Frame.ref parent) ∧
        Canonical.cellAt result (Frame.ref parent) = .ok ((Frame.ofMountain p.reduced).cell parent)) := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hOne := Frame.one_le_height hNormal.toOrdered hReal
  have hSourceFront : frontierAt hNormal.toOrdered (F.height source) hOne candidate.1 = candidate :=
    frontierAt_eq_of_upper_barrier hNormal.toOrdered hOne
      (Frame.Q_height_le hNormal.toOrdered hCandidate)
      (fun _ hUpper => Frame.Q_upper_gt hNormal.toOrdered hCandidate hUpper)
  have hUnmarked := copy.state.high_source_not_marked hLast source.1.isLt
    copy.data copy.read.source_at hHigh
  have hNoPremature := (copy.state.column_data_parent_inputs hLast source.1.isLt copy.data).1
  obtain ⟨copied, hCopy, hShape⟩ := copy.read.nonmarker_copy_execution hNoPremature hUnmarked
  obtain ⟨actualSource, actualCandidate, hSourceRef, hSourceCell, hQ, hSearch,
      hColumn, hCut, hFront⟩ := copy.candidate_frontier_all_columns hValid hReal hCopy hShape hCandidate
  have hRow := copy.high_row hLast hHigh
  have hActualFront : frontierAt hValid.toOrdered (F.height source) hOne actualCandidate.1 =
      actualCandidate := by simpa only [hRow] using hFront
  obtain ⟨_, boundary, hBoundaryColumn, _, hBoundaryFront, _, hParents, _⟩ :=
    p.blocks_reduced_root_frontier_correspondence hLast hStartRun hOne hHigh hRoot hSourceFront
  have hValue := p.blocks_root_value_at_frontiers hLast hStartRun copy.state.start_valid
    hOne hHigh hRoot hSourceFront hBoundaryColumn hBoundaryFront
  have hPreserved : PreservesColumns start result := copy.state.start_preserved.trans
    ((PreservesColumns.push copy.before copy.column).trans copy.preserved)
  let expected := hPreserved.mapNode boundary
  have hExpectedFront := frontierAt_of_same_column copy.state.start_valid.toOrdered hValid.toOrdered
    hOne hBoundaryFront (hPreserved.mapNode_ref boundary) (hPreserved _ boundary.1.isLt)
  have hActualColumn : actualCandidate.1.val = p.root.column +
      block * (p.reduced.size - 1 - p.root.column) := by
    simpa only [hRoot, lt_self_iff_false, if_false] using hColumn
  have hColumns : expected.1 = actualCandidate.1 := by
    apply Fin.ext
    have hMap := hPreserved.mapNode_column boundary
    have hSize := copy.state.start_size
    change expected.1.val = _ at hMap ⊢
    omega
  have he : actualCandidate = expected := by
    rw [hColumns, hActualFront] at hExpectedFront
    exact hExpectedFront
  have hRef : Frame.ref actualCandidate = Frame.ref boundary := he ▸ hPreserved.mapNode_ref boundary
  have hCell : G.cell actualCandidate = (Frame.ofMountain start).cell boundary :=
    he ▸ hPreserved.mapNode_cell boundary
  refine ⟨actualSource, actualCandidate, hSourceRef, hSourceCell, hQ, hSearch,
    (congrArg Cell.value hCell).trans hValue, ?_⟩
  intro parent hParent
  obtain ⟨hFixed, hEdge, hRead⟩ := hParents parent hParent
  refine ⟨hFixed, ?_, ?_⟩
  · simpa only [hRef] using hEdge.preserve hPreserved
  · exact (hPreserved.cellAt (by
      change parent.1.val < start.size
      have hSize := copy.state.start_size
      omega)).trans hRead

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent result)

/-- If the old first candidate is in the root column, its actual boundary
replacement supplies the first record. When the source last blocker is
that root candidate, the replacement itself is the new last blocker and
its equal value proves the barrier. Otherwise its first actual P edge
joins the fully preserved good-prefix record tail. -/
theorem recognize_high_root_candidate
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies startCopies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hRoot : packet.candidate.1.val = p.root.column)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (hHigher : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hPreserved := p.expandDiagram_reduced_preserved hLast hCopies hRun
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered packet.source_parent).1.trans
      (Frame.P_value hNormal.toOrdered packet.source_parent).2)
  obtain ⟨u, candidate, hURef, _, hQ, _, hValue, hEdges⟩ :=
    packet.pair.uCopy.candidate_high_root_records hLast hValid hStartRun hSourceReal hHigh
      packet.source_candidate hRoot
  have heU : u = packet.pair.u := Executable.ref_injective G (hURef.trans packet.pair.u_ref.symm)
  subst u
  have hZLe : packet.blocker.1.val ≤ p.root.column :=
    (packet.source_path.column_le hNormal.toOrdered).trans_eq hRoot
  have hParentFixed : sourceParent.1.val < p.root.column :=
    (Frame.P_column_lt hNormal.toOrdered packet.source_last_parent).trans_le hZLe
  have hZSource : Frame.ref packet.pair.z = Frame.ref packet.blocker ∧
      G.cell packet.pair.z = F.cell packet.blocker := by
    rcases packet.pair.z_origin with ⟨_, hRef, hCell⟩ | ⟨hRight, _⟩
    · exact ⟨hRef, hCell⟩
    · exact False.elim (not_lt_of_ge hZLe hRight)
  have hParentRef : Frame.ref packet.pair.parent = Frame.ref sourceParent := by
    rcases packet.pair.parent_origin with ⟨_, hRef, _⟩ | ⟨hRootParent, _⟩ | ⟨hRight, _⟩
    · exact hRef
    · exact False.elim (ne_of_lt hParentFixed hRootParent)
    · exact False.elim (not_lt_of_ge hParentFixed.le hRight)
  have heZ : hPreserved.mapNode packet.blocker = packet.pair.z :=
    Executable.ref_injective G ((hPreserved.mapNode_ref packet.blocker).trans hZSource.1.symm)
  have heParent : hPreserved.mapNode sourceParent = packet.pair.parent :=
    Executable.ref_injective G ((hPreserved.mapNode_ref sourceParent).trans hParentRef.symm)
  have hQReal := Frame.Q_real hValid.toOrdered packet.pair.u_real hQ
  have hQLeft := Frame.Q_column_lt hValid.toOrdered hQ
  have hBoundaryP : ∀ parent, F.P packet.candidate = some parent →
      G.P candidate = some (hPreserved.mapNode parent) := by
    intro parent hParent
    obtain ⟨_, hEdge, _⟩ := hEdges parent hParent
    exact hLeft candidate (hPreserved.mapNode parent) hQLeft hQReal
      (hEdge.rawParent rfl (hPreserved.mapNode_ref parent))
  have hUpperLt : F.height sourceU < F.height packet.sourceUUpper := by
    have hUpper := packet.source_u_upper
    rcases sourceU with ⟨c, i⟩
    unfold Frame.upper at hUpper
    split at hUpper
    · obtain he := Option.some.inj hUpper
      rw [← he]
      exact hNormal.toOrdered.rows_strict c (show i.val < i.val + 1 by omega)
    · cases hUpper
  have hBarrier := packet.high_upper_barrier hLast hLegal hCopies hRun
    (hHigh.trans hUpperLt.le) hLeft hHigher
  have hSmall := ((expandDiagram_equations hLegal hRun).1.rawParent_value_lt
    hValid packet.pair.u_real packet.pair.u_parent).2
  by_cases hSame : packet.candidate = packet.blocker
  · have hSourceP : F.P packet.candidate = some sourceParent :=
      hSame ▸ packet.source_last_parent
    have hLast := hBoundaryP sourceParent hSourceP
    rw [heParent] at hLast
    have hSameValue : G.value candidate = G.value packet.pair.z :=
      hValue.trans ((congrArg F.value hSame).trans (congrArg Cell.value hZSource.2).symm)
    exact Frame.P_of_record_barrier hValid.toOrdered hQ (.refl _) hLast
      (hBarrier.trans_eq hSameValue.symm) hSmall
  · obtain ⟨next, hFirstParent, rest⟩ := root_candidate_path_first packet.source_path hSame
    have hPath := hPreserved.mapNode_parentPath hNormal.toOrdered hValid.toOrdered rest
    rw [heZ] at hPath
    have hLast := hPreserved.mapNode_P hNormal.toOrdered hValid.toOrdered packet.source_last_parent
    rw [heZ, heParent] at hLast
    exact Frame.P_of_record_barrier hValid.toOrdered hQ
      (.cons (hBoundaryP next hFirstParent) hPath) hLast hBarrier hSmall

end AnySourceBlockerPacket

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_high_root_records
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.recognize_high_root_candidate
