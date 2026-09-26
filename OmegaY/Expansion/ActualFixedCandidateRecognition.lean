/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFixedCandidateRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighFixedCandidateRecognition
import OmegaY.Expansion.ActualFixedBlockerValue
import OmegaY.Canonical.BottomLegs

/-!
# Actual numerical recognition with a fixed source candidate

A source Q in the good prefix forces the current effective row to remain
unchanged: its incoming source edge has a fixed numerical parent. The
actual target candidate and its entire record path are therefore preserved
source nodes. Exact fixed-parent values supply the last-record barrier.
No target numerical induction or high-row restriction is used here.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source candidate : (Frame.ofMountain p.reduced).Node}
  (copy : EffectiveCopyOccurrence p block start references source result)

include copy

omit copy in
theorem unmarked_of_fixed_candidate
    (hReal : Real source)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hFixed : candidate.1.val < p.root.column) :
    source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index := by
  have hNormal := build_normal_of_success p.reduced_build
  have hNot : ¬ BucketMem p.marked source.1.val (Frame.ref source) := by
    cases hp : (Frame.ofMountain p.reduced).P source with
    | some parent =>
        obtain ⟨q, hq, trace⟩ := (P_iff hNormal.toOrdered).mp hp
        have he : q = candidate := Option.some.inj (hq.symm.trans hCandidate)
        subst q
        exact p.fixed_parent_not_marked hp ((trace.column_le hNormal.toOrdered).trans_lt hFixed)
    | none =>
        intro hMarked
        obtain ⟨root, hRootRef, _⟩ := Canonical.frame_node_of_cellAt p.restored_root
        have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := by
          simpa only [hRootRef] using p.markers_built
        obtain ⟨hRight, low, _, hColumn, _, hPath, _⟩ :=
          (build_markers_real_member_iff_parentPath p.reduced_build hMarkers hReal).mp hMarked
        cases hPath with
        | refl => have hc := congrArg Fin.val hColumn; omega
        | cons hParent _ => rw [hp] at hParent; cases hParent
  intro h
  obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
  have he : marker = Frame.ref source := congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
  exact hNot (he ▸ hm)

theorem stationary_of_fixed_candidate (hLast : 1 < last)
    (hReal : Real source)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hFixed : candidate.1.val < p.root.column) :
    copy.read.outputCell.row = (Frame.ofMountain p.reduced).height source := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨stored, hStored, _, _, hCandidateColumn, _⟩ := Q_spec hNormal.toOrdered hCandidate
  have hSourceRight : p.root.column < source.1.val := copy.state.next_lower
  have hIndex : 1 < source.2.val := by
    by_contra hn
    have hi : source.2.val = 1 := by change 0 < source.2.val at hReal; omega
    have hiBound : 1 < F.length source.1 := by dsimp [F]; have := source.2.isLt; omega
    have hIndexEq : source.2 = ⟨1, hiBound⟩ := Fin.ext hi
    have hBottom := build_bottom_left p.reduced_build source.1 hiBound
    have hPositive : source.1.val ≠ 0 := by omega
    change (F.cells source.1 source.2).left = some (Frame.ref stored) at hStored
    rw [hIndexEq, hBottom, if_neg hPositive] at hStored
    have hc := congrArg Ref.column (Option.some.inj hStored)
    have hcc := congrArg Fin.val hCandidateColumn
    change source.1.val - 1 = stored.1.val at hc
    omega
  let lower : F.Node := ⟨source.1, ⟨source.2.val - 1, by dsimp [F]; have := source.2.isLt; omega⟩⟩
  have hLowerReal : Real lower := by change 0 < source.2.val - 1; omega
  have hUpper : F.upper lower = some source := by
    apply Frame.upper_of_refs (before := lower) (after := source) rfl
    apply congrArg (Ref.mk source.1.val)
    change source.2.val = source.2.val - 1 + 1
    omega
  obtain ⟨parent, hParent, _, _, hLeft⟩ := hNormal.upper_step lower source hLowerReal hUpper
  have he : parent = stored := Executable.ref_injective F
    (Option.some.inj (hLeft.symm.trans hStored))
  have hParentFixed : parent.1.val < p.root.column := by
    rw [he, ← hCandidateColumn]
    exact hFixed
  obtain ⟨lowerCopy⟩ := copy.in_same_column hLast (other := lower) rfl
  obtain ⟨actualUpper, hRead, hRow⟩ := lowerCopy.fixed_parent_upper_read hLast hParent hParentFixed hUpper
  obtain ⟨effectiveUpper, hEffectiveRead, hEffectiveRow⟩ := lowerCopy.effective_upper_row_all
    hLast hLowerReal copy hUpper (unmarked_of_fixed_candidate hReal hCandidate hFixed)
  have hEqual : actualUpper = effectiveUpper := Except.ok.inj (hRead.symm.trans hEffectiveRead)
  exact hEffectiveRow.symm.trans (hEqual ▸ hRow)

theorem candidate_eq_fixed
    (hLast : 1 < last) (hValid : MountainValid result)
    (hPreserved : PreservesColumns p.reduced result) (hReal : Real source)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hFixed : candidate.1.val < p.root.column) :
    ∃ actualSource : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      (Frame.ofMountain result).cell actualSource = copy.read.outputCell ∧
      (Frame.ofMountain result).Q actualSource = some (hPreserved.mapNode candidate) ∧
      nextCandidate result copy.outputRef = .ok (Frame.ref candidate) := by
  have hNormal := build_normal_of_success p.reduced_build
  have hUnmarked := unmarked_of_fixed_candidate hReal hCandidate hFixed
  have hNoPremature := (copy.state.column_data_parent_inputs hLast source.1.isLt copy.data).1
  obtain ⟨copied, hCopy, hShape⟩ := copy.read.nonmarker_copy_execution hNoPremature hUnmarked
  obtain ⟨actualSource, actualCandidate, hRef, hCell, hQ, hSearch, hColumn, hCut, hFront⟩ :=
    copy.candidate_frontier_all_columns hValid hReal hCopy hShape hCandidate
  have hRow := copy.stationary_of_fixed_candidate hLast hReal hCandidate hFixed
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

end EffectiveCopyOccurrence

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent result)

/-- The actual last record is on the preserved target candidate path, and
its numerical barrier follows from exact fixed-parent values. Neither a
new-path premise nor any target numerical recognition hypothesis occurs. -/
theorem recognize_fixed_candidate
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hFixed : packet.candidate.1.val < p.root.column) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hPreserved := p.expandDiagram_reduced_preserved hLast hCopies hRun
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered packet.source_parent).1.trans
      (Frame.P_value hNormal.toOrdered packet.source_parent).2)
  obtain ⟨u, hURef, _, hQ, _⟩ := packet.pair.uCopy.candidate_eq_fixed
    hLast hValid hPreserved hSourceReal packet.source_candidate hFixed
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
  have hBarrier := packet.fixed_parent_barrier hLast hLegal hRun hParentFixed
  have hSmall := ((expandDiagram_equations hLegal hRun).1.rawParent_value_lt
    hValid packet.pair.u_real packet.pair.u_parent).2
  exact Frame.P_of_record_barrier hValid.toOrdered hQ hPath hLastParent hBarrier hSmall

theorem findParent_fixed_candidate
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hFixed : packet.candidate.1.val < p.root.column) :
    findParent result packet.pair.uCopy.outputRef = .ok (Frame.ref sourceParent) := by
  have hP := packet.recognize_fixed_candidate hLast hLegal hCopies hRun hFixed
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

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.unmarked_of_fixed_candidate
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.stationary_of_fixed_candidate
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_eq_fixed
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.recognize_fixed_candidate
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.findParent_fixed_candidate
