/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighFixedCandidateRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualAnyHighCandidate
import OmegaY.Expansion.ActualAnyHighBarrier
import OmegaY.Expansion.PreservedSearchNodes

/-!
# Numerical recognition when a high node's first source Q is fixed

The source record chain then lies entirely in the unchanged good prefix.
Actual copy execution identifies the target Q, and complete-column search
locality transports that whole record chain. The high value barrier is
applied to the actual last record of this path, not to a disconnected
unchanged comparison node. Only the stated strict-left/strictly-higher
numerical induction hypotheses enter the value-barrier argument.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem PreservesColumns.mapNode_parentPath {before after : Mountain}
    (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    {source target : (Frame.ofMountain before).Node}
    (path : ParentPath (Frame.ofMountain before) source target) :
    ParentPath (Frame.ofMountain after) (h.mapNode source) (h.mapNode target) := by
  induction path with
  | refl _ => exact .refl _
  | cons hParent _ ih => exact .cons (h.mapNode_P hBefore hAfter hParent) ih

/-- A high own-cell copy with its source Q in the good prefix has that
exact original node as its actual Q. Both its reference and full cell are
identified from preserved reads. -/
theorem EffectiveCopyOccurrence.candidate_eq_high_fixed
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start result : Mountain} {references : List Ref}
    {source candidate : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last) (hValid : MountainValid result)
    (hPreserved : PreservesColumns p.reduced result) (hReal : Real source)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height source)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hFixed : candidate.1.val < p.root.column) :
    ∃ actualSource : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      (Frame.ofMountain result).cell actualSource = copy.read.outputCell ∧
      (Frame.ofMountain result).Q actualSource = some (hPreserved.mapNode candidate) ∧
      nextCandidate result copy.outputRef = .ok (Frame.ref candidate) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hUnmarked := copy.state.high_source_not_marked hLast source.1.isLt
    copy.data copy.read.source_at hHigh
  have hNoPremature := (copy.state.column_data_parent_inputs hLast source.1.isLt copy.data).1
  obtain ⟨copied, hCopy, hShape⟩ := copy.read.nonmarker_copy_execution hNoPremature hUnmarked
  obtain ⟨actualSource, actualCandidate, hRef, hCell, hQ, hSearch, hColumn, hCut, hFront⟩ :=
    copy.candidate_frontier_all_columns hValid hReal hCopy hShape hCandidate
  have hRow := copy.high_row hLast hHigh
  have hOne := Frame.one_le_height hNormal.toOrdered hReal
  have hOldFront : frontierAt hNormal.toOrdered ((Frame.ofMountain p.reduced).height source)
      hOne candidate.1 = candidate :=
    frontierAt_eq_of_upper_barrier hNormal.toOrdered hOne
      (Q_height_le hNormal.toOrdered hCandidate)
      (fun _ hUpper => Q_upper_gt hNormal.toOrdered hCandidate hUpper)
  have hExpectedFront := frontierAt_of_same_column hNormal.toOrdered hValid.toOrdered hOne
    hOldFront (hPreserved.mapNode_ref candidate) (hPreserved _ candidate.1.isLt)
  have hFront' : frontierAt hValid.toOrdered ((Frame.ofMountain p.reduced).height source)
      hOne actualCandidate.1 = actualCandidate := by simpa only [hRow] using hFront
  have hColumn' : actualCandidate.1.val = candidate.1.val := by
    simpa only [if_pos hFixed] using hColumn
  have hc : (hPreserved.mapNode candidate).1 = actualCandidate.1 :=
    Fin.ext ((hPreserved.mapNode_column candidate).trans hColumn'.symm)
  have he : actualCandidate = hPreserved.mapNode candidate := by
    rw [hc, hFront'] at hExpectedFront
    exact hExpectedFront
  refine ⟨actualSource, hRef, hCell, he ▸ hQ, ?_⟩
  simpa only [he, hPreserved.mapNode_ref] using hSearch

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent result)

/-- The nondirect fixed-Q branch is genuinely recognized. The actual
last blocker is the preserved source blocker, on the actual target record
path, and its value barrier is proved rather than supplied. -/
theorem recognize_high_fixed_candidate
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hFixed : packet.candidate.1.val < p.root.column)
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
  obtain ⟨u, hURef, _, hQ, _⟩ := packet.pair.uCopy.candidate_eq_high_fixed
    hLast hValid hPreserved hSourceReal hHigh packet.source_candidate hFixed
  have heU : u = packet.pair.u := Executable.ref_injective G (hURef.trans packet.pair.u_ref.symm)
  subst u
  have hZFixed : packet.blocker.1.val < p.root.column :=
    (packet.source_path.column_le hNormal.toOrdered).trans_lt hFixed
  have hParentFixed : sourceParent.1.val < p.root.column :=
    (Frame.P_column_lt hNormal.toOrdered packet.source_last_parent).trans hZFixed
  have hZRef : Frame.ref packet.pair.z = Frame.ref packet.blocker := by
    rcases packet.pair.z_origin with ⟨_, hRef, _⟩ | ⟨hRight, _⟩
    · exact hRef
    · exact False.elim (not_lt_of_ge hZFixed.le hRight)
  have hParentRef : Frame.ref packet.pair.parent = Frame.ref sourceParent := by
    rcases packet.pair.parent_origin with ⟨_, hRef, _⟩ | ⟨hRoot, _⟩ | ⟨hRight, _⟩
    · exact hRef
    · exact False.elim (ne_of_lt hParentFixed hRoot)
    · exact False.elim (not_lt_of_ge hParentFixed.le hRight)
  have heZ : hPreserved.mapNode packet.blocker = packet.pair.z :=
    Executable.ref_injective G ((hPreserved.mapNode_ref packet.blocker).trans hZRef.symm)
  have heParent : hPreserved.mapNode sourceParent = packet.pair.parent :=
    Executable.ref_injective G ((hPreserved.mapNode_ref sourceParent).trans hParentRef.symm)
  have hPath := hPreserved.mapNode_parentPath hNormal.toOrdered hValid.toOrdered packet.source_path
  rw [heZ] at hPath
  have hLastParent := hPreserved.mapNode_P hNormal.toOrdered hValid.toOrdered packet.source_last_parent
  rw [heZ, heParent] at hLastParent
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
  exact Frame.P_of_record_barrier hValid.toOrdered hQ hPath hLastParent hBarrier hSmall

theorem findParent_high_fixed_candidate
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hFixed : packet.candidate.1.val < p.root.column)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height sourceU)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (hHigher : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father) :
    findParent result packet.pair.uCopy.outputRef = .ok (Frame.ref sourceParent) := by
  have hP := packet.recognize_high_fixed_candidate hLast hLegal hCopies hRun hFixed hHigh hLeft hHigher
  have hNormal := build_normal_of_success p.reduced_build
  have hParentFixed : sourceParent.1.val < p.root.column :=
    (Frame.P_column_lt hNormal.toOrdered packet.source_last_parent).trans_le
      (packet.source_path.column_le hNormal.toOrdered) |>.trans hFixed
  have hParentRef : Frame.ref packet.pair.parent = Frame.ref sourceParent := by
    rcases packet.pair.parent_origin with ⟨_, hRef, _⟩ | ⟨hRoot, _⟩ | ⟨hRight, _⟩
    · exact hRef
    · exact False.elim (ne_of_lt hParentFixed hRoot)
    · exact False.elim (not_lt_of_ge hParentFixed.le hRight)
  simpa only [packet.pair.u_ref, hParentRef] using
    (Executable.findParent_ref_iff (expandDiagram_valid_of_success hLegal hRun).toOrdered _ _).mpr hP

end AnySourceBlockerPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.mapNode_parentPath
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_high_fixed
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.recognize_high_fixed_candidate
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.findParent_high_fixed_candidate
