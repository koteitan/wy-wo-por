/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighCurrentRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighRecordTransport

/-!
# Numerical recognition of all nondirect high-current source copies

The real within-block history transports every source record at the current
high cut. Later complete-column preservation puts this path in the actual
final output, even for a copy from an earlier block. A root-column blocker
is replaced by its actual equal-valued boundary frontier; the old root
node is never silently inserted into the new search path.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem high_current_frontier_self {F : Frame} (hF : F.Ordered)
    (u : F.Node) (hOne : (1 : Row) ≤ F.height u) :
    frontierAt hF (F.height u) hOne u.1 = u := by
  apply frontierAt_eq_of_upper_barrier hF hOne le_rfl
  intro upper hUpper
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain he := Option.some.inj hUpper
    rw [← he]
    exact hF.rows_strict c (show i.val < i.val + 1 by omega)
  · cases hUpper

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent result)

/-- All source-candidate and source-parent columns are covered. The only
target numerical hypotheses concern strictly left columns and strictly
higher nodes of the current column. The actual path and last-blocker
inequality are conclusions of execution and the high transport theorem. -/
theorem recognize_high_current
    {before : Mountain} {next : Nat}
    (s : DynamicBlockState p block start references next before)
    (history : CopyRunHistory p block start references next before)
    (hPreserved : PreservesColumns before result)
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies startCopies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hBefore : sourceU.1.val < next)
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
  have hSourceReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered packet.source_parent).1.trans
      (Frame.P_value hNormal.toOrdered packet.source_parent).2)
  have hOne := Frame.one_le_height hNormal.toOrdered hSourceReal
  have hSourceFront := high_current_frontier_self hNormal.toOrdered sourceU hOne
  have hQBefore := (Frame.Q_column_lt hNormal.toOrdered packet.source_candidate).trans hBefore
  have hZBefore := packet.blocker_before.trans hBefore
  have hPBefore := (Frame.P_column_lt hNormal.toOrdered packet.source_parent).trans hBefore
  let image := fun (node : F.Node) (hn : node.1.val < next) =>
    hPreserved.mapNode (s.recordFrontier (F.height sourceU) hOne node hn)
  have hImageColumn : ∀ (node : F.Node) (hn : node.1.val < next),
      (image node hn).1.val = copiedColumnIndex p.root.column
        (block * (p.reduced.size - 1 - p.root.column)) node.1.val := by
    intro node hn
    exact (hPreserved.mapNode_column _).trans (s.recordFrontier_column _ hOne node hn)
  have hImageFront : ∀ (node : F.Node) (hn : node.1.val < next),
      frontierAt hValid.toOrdered (F.height sourceU) hOne (image node hn).1 = image node hn := by
    intro node hn
    exact frontierAt_of_same_column s.ambient_valid.toOrdered hValid.toOrdered hOne
      (s.recordFrontier_at _ hOne node hn) (hPreserved.mapNode_ref _)
      (hPreserved _ (s.recordFrontier _ hOne node hn).1.isLt)
  have hImageReal : ∀ (node : F.Node) (hn : node.1.val < next), Real (image node hn) :=
    fun node hn => hPreserved.mapNode_real (s.recordFrontier_real _ hOne node hn)
  have hURow : G.height packet.pair.u = F.height sourceU := by
    change (G.cell packet.pair.u).row = _
    rw [packet.pair.u_cell, packet.pair.uCopy.high_row hLast hHigh]
  have hUFront : frontierAt hValid.toOrdered (F.height sourceU) hOne packet.pair.u.1 = packet.pair.u := by
    have hh := high_current_frontier_self hValid.toOrdered packet.pair.u
      (Frame.one_le_height hValid.toOrdered packet.pair.u_real)
    change frontierAt hValid.toOrdered (G.height packet.pair.u) _ packet.pair.u.1 = packet.pair.u at hh
    simpa only [hURow] using hh
  have hUColumn : (image sourceU hBefore).1 = packet.pair.u.1 := by
    apply Fin.ext
    rw [hImageColumn]
    simp only [copiedColumnIndex, if_neg (not_lt_of_ge packet.pair.uCopy.state.next_lower.le)]
    exact ((congrArg Ref.column packet.pair.u_ref).trans packet.pair.uCopy.source_column).symm
  have heU : image sourceU hBefore = packet.pair.u := by
    have hh := hImageFront sourceU hBefore
    rw [hUColumn, hUFront] at hh
    exact hh.symm
  have hUnmarked := packet.pair.uCopy.state.high_source_not_marked hLast sourceU.1.isLt
    packet.pair.uCopy.data packet.pair.uCopy.read.source_at hHigh
  have hNoPrem := (packet.pair.uCopy.state.column_data_parent_inputs hLast sourceU.1.isLt
    packet.pair.uCopy.data).1
  obtain ⟨copied, hCopy, hShape⟩ := packet.pair.uCopy.read.nonmarker_copy_execution hNoPrem hUnmarked
  obtain ⟨actualU, actualQ, hURef, _, hActualQ, _, hQColumn, hQOne, hQFront⟩ :=
    packet.pair.uCopy.candidate_frontier_all_columns hValid hSourceReal hCopy hShape packet.source_candidate
  have heActualU : actualU = packet.pair.u :=
    Executable.ref_injective G (hURef.trans packet.pair.u_ref.symm)
  subst actualU
  have hQFront' : frontierAt hValid.toOrdered (F.height sourceU) hOne actualQ.1 = actualQ := by
    simpa only [packet.pair.uCopy.high_row hLast hHigh] using hQFront
  have hQColumns : (image packet.candidate hQBefore).1 = actualQ.1 :=
    Fin.ext ((hImageColumn _ _).trans hQColumn.symm)
  have heQ : image packet.candidate hQBefore = actualQ := by
    have hh := hImageFront packet.candidate hQBefore
    rw [hQColumns, hQFront'] at hh
    exact hh.symm
  have hQ : G.Q packet.pair.u = some (image packet.candidate hQBefore) := heQ ▸ hActualQ
  have hSourceQFront : frontierAt hNormal.toOrdered (F.height sourceU) hOne packet.candidate.1 =
      packet.candidate := frontierAt_eq_of_upper_barrier hNormal.toOrdered hOne
        (Frame.Q_height_le hNormal.toOrdered packet.source_candidate)
        (fun _ hUpper => Frame.Q_upper_gt hNormal.toOrdered packet.source_candidate hUpper)
  have hSourceZFront : frontierAt hNormal.toOrdered (F.height sourceU) hOne packet.blocker.1 =
      packet.blocker := by
    apply frontierAt_eq_of_upper_barrier hNormal.toOrdered hOne packet.source_lower
    intro upper hUpper
    have he := Option.some.inj (hUpper.symm.trans packet.source_z_upper)
    exact he ▸ packet.source_overlap
  have hRawU := hPreserved.mapNode_rawParent (s.high_record_parent history hLast hStartRun
    hOne hHigh hBefore hPBefore hSourceFront packet.source_parent)
  change G.rawParent (image sourceU hBefore) = some (image sourceParent hPBefore) at hRawU
  rw [heU] at hRawU
  have heParent : image sourceParent hPBefore = packet.pair.parent :=
    Option.some.inj (hRawU.symm.trans packet.pair.u_parent)
  have hRawPath := (s.high_record_path history hLast hStartRun hOne hHigh hQBefore hZBefore
    hSourceQFront packet.source_path).preserve hPreserved
  have hQReal := Frame.Q_real hValid.toOrdered packet.pair.u_real hQ
  have hQLeft := Frame.Q_column_lt hValid.toOrdered hQ
  have hPath := hRawPath.toParentPath_of_recognition hValid.toOrdered hLeft
    (hPreserved.mapNode_ref _) (hPreserved.mapNode_ref _) hQReal hQLeft
  change ParentPath G (image packet.candidate hQBefore) (image packet.blocker hZBefore) at hPath
  have hRawZ := hPreserved.mapNode_rawParent (s.high_record_parent history hLast hStartRun
    hOne hHigh hZBefore hPBefore hSourceZFront packet.source_last_parent)
  change G.rawParent (image packet.blocker hZBefore) = some (image sourceParent hPBefore) at hRawZ
  rw [heParent] at hRawZ
  have hLastP := hLeft (image packet.blocker hZBefore) packet.pair.parent
    ((hPath.column_le hValid.toOrdered).trans_lt hQLeft) (hImageReal _ _) hRawZ
  have hZValue : G.value (image packet.blocker hZBefore) = G.value packet.pair.z := by
    have hMappedCell := hPreserved.mapNode_cell (s.recordFrontier (F.height sourceU) hOne packet.blocker hZBefore)
    change G.cell (image packet.blocker hZBefore) = _ at hMappedCell
    by_cases hFixed : packet.blocker.1.val < p.root.column
    · have hSourceCell := (s.recordFrontier_fixed hOne hZBefore hSourceZFront hFixed).2
      rcases packet.pair.z_origin with ⟨_, _, hCell⟩ | ⟨hRight, _⟩
      · exact congrArg Cell.value ((hMappedCell.trans hSourceCell).trans hCell.symm)
      · exact False.elim (not_lt_of_ge hFixed.le hRight)
    · by_cases hRoot : packet.blocker.1.val = p.root.column
      · have hRootValue := (s.recordFrontier_root hLast hStartRun hOne hHigh hZBefore hSourceZFront hRoot).1
        rcases packet.pair.z_origin with ⟨_, _, hCell⟩ | ⟨hRight, _⟩
        · exact ((congrArg Cell.value hMappedCell).trans hRootValue).trans (congrArg Cell.value hCell).symm
        · exact False.elim (ne_of_gt hRight hRoot)
      · have hRight : p.root.column < packet.blocker.1.val :=
          lt_of_le_of_ne (Nat.le_of_not_gt hFixed) (Ne.symm hRoot)
        rcases packet.pair.z_origin with ⟨hLeft, _⟩ | ⟨_, zCopy, _, hCell⟩
        · exact False.elim (not_lt_of_ge hLeft hRight)
        · obtain ⟨oldCopy⟩ := s.prior_effective_occurrence history hLast hRight hZBefore
          have hSourceCell := (s.recordFrontier_copied hLast hOne hHigh hZBefore hSourceZFront hRight oldCopy).2
          have hCopyCell := ((oldCopy.extend hPreserved).unique zCopy).2
          exact congrArg Cell.value ((hMappedCell.trans hSourceCell).trans (hCopyCell.trans hCell.symm))
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
  exact Frame.P_of_record_barrier hValid.toOrdered hQ hPath hLastP
    (hBarrier.trans_eq hZValue.symm) hSmall

end AnySourceBlockerPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.AnySourceBlockerPacket.recognize_high_current
