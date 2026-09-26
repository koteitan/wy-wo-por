/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighestRootCandidateRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowRootCandidateRecognition
import OmegaY.Expansion.ActualHighRootValue
import OmegaY.Expansion.PreservedDepthWords

/-!
# Last records of the highest root boundary at earlier cuts

The highest selector has the bad root's value and its original fixed
parent. A recognized completed-block prefix projects this actual edge to
an earlier cut, retaining the projection's value barrier. The projected
last record replaces the old bad-root record; a path through the original
bad-root node is neither assumed nor needed.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem path_last {F : Frame} {source target : F.Node}
    (path : ParentPath F source target) (hNe : source ≠ target) :
    ∃ last, ParentPath F source last ∧ F.P last = some target := by
  induction path with
  | refl _ => exact (hNe rfl).elim
  | @cons source next target hParent tail ih =>
    by_cases he : next = target
    · exact ⟨source, .refl _, he ▸ hParent⟩
    · obtain ⟨last, path, edge⟩ := ih he
      exact ⟨last, .cons hParent path, edge⟩

private theorem path_first {F : Frame} {source target : F.Node}
    (path : ParentPath F source target) (hNe : source ≠ target) :
    ∃ next, F.P source = some next ∧ ParentPath F next target := by
  cases path with
  | refl _ => exact (hNe rfl).elim
  | cons hParent tail => exact ⟨_, hParent, tail⟩

private theorem build_cut_parent_last_record {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {selected parent : (Frame.ofMountain mountain).Node}
    (hParent : (Frame.ofMountain mountain).P selected = some parent)
    {low high : Row} (hLow : (1 : Row) ≤ low) (hOrder : low ≤ high)
    (hSelected : frontierAt (build_normal_of_success hBuild).toOrdered high
      (hLow.trans hOrder) selected.1 = selected)
    (hParentFront : frontierAt (build_normal_of_success hBuild).toOrdered low hLow parent.1 = parent) :
    ∃ z, ParentPath (Frame.ofMountain mountain)
        (frontierAt (build_normal_of_success hBuild).toOrdered low hLow selected.1) z ∧
      (Frame.ofMountain mountain).P z = some parent ∧
      (Frame.ofMountain mountain).value selected ≤ (Frame.ofMountain mountain).value z := by
  let F := Frame.ofMountain mountain
  have hNormal := build_normal_of_success hBuild
  obtain ⟨earlier, hEarlier, hEarlierCut, _, hEarlierFront⟩ := event_floor_at_cut hNormal.toOrdered hLow
  obtain ⟨event, hEvent, _, hEventMax, hEventFront⟩ := event_floor_at_cut hNormal.toOrdered (hLow.trans hOrder)
  have hEventOrder : earlier ≤ event := eventCut_index_le hEarlier
    (hEventMax _ (F.eventCut_mem earlier) (hEarlierCut.trans hOrder))
  have hAt : F.P (eventFrontier hNormal.toOrdered event selected.1) = some parent := by
    rw [hEventFront, hSelected]
    exact hParent
  have hBound : mountain.size - 1 < mountain.size := by omega
  obtain ⟨path, hColumn, hBarrier⟩ := build_event_parent_projection hBuild hWidth hBound hEventOrder
    hEvent selected.1 (Nat.le_sub_one_of_lt selected.1.isLt) hAt
  rw [hEarlierFront, hEarlierFront, hParentFront] at path
  have hNe : frontierAt hNormal.toOrdered low hLow selected.1 ≠ parent := by
    intro he
    have hc := congrArg (fun node : F.Node => node.1.val) he
    rw [congrArg Fin.val (frontierAt_spec hNormal.toOrdered hLow selected.1).1] at hc
    exact (ne_of_lt hColumn) hc.symm
  obtain ⟨z, hPath, hLast⟩ := path_last path hNe
  have hBarrierZ := (hBarrier z (by simpa only [hEarlierFront] using hPath)
    (P_column_lt hNormal.toOrdered hLast)).2.2
  rw [hEventFront, hSelected] at hBarrierZ
  exact ⟨z, hPath, hLast, hBarrierZ⟩

theorem Preparation.blocks_highest_root_records_at_cut
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {start ambient : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hPreserved : PreservesColumns start ambient) (hAmbient : (Frame.ofMountain ambient).Ordered)
    (hKnown : ∀ (node father : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some father →
        (Frame.ofMountain ambient).P node = some father)
    {root parent : (Frame.ofMountain p.reduced).Node}
    (hRoot : Frame.ref root = p.root) (hParent : (Frame.ofMountain p.reduced).P root = some parent)
    (hStartValid : MountainValid start) (hWidth : 0 < start.size)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hLow : (Frame.ofMountain p.reduced).height root ≤ cut) (hHigh : cut < p.lastTop.row) :
    ∃ originalParent z : (Frame.ofMountain start).Node,
      Frame.ref originalParent = Frame.ref parent ∧
      (Frame.ofMountain start).cell originalParent = (Frame.ofMountain p.reduced).cell parent ∧
      ParentPath (Frame.ofMountain start)
        (frontierAt hStartValid.toOrdered cut hCut ⟨start.size - 1, by
          change start.size - 1 < start.size; omega⟩) z ∧
      (Frame.ofMountain start).P z = some originalParent ∧
      (Frame.ofMountain p.reduced).value root ≤ (Frame.ofMountain start).value z := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain start
  have hSourceNormal := build_normal_of_success p.reduced_build
  obtain ⟨values, _, hBuild⟩ := p.blocks_reconstruct_of_left_recognition
    hLast hRun hPreserved hAmbient hKnown
  have hNormal := build_normal_of_success hBuild
  obtain ⟨output, hOutput, ready⟩ := p.blocks_total hLast copies
  have he : output = start := Except.ok.inj (hOutput.symm.trans hRun)
  subst output
  let original := ready.base_preserved.mapNode parent
  have hOriginalRef := ready.base_preserved.mapNode_ref parent
  have hOriginalCell := ready.base_preserved.mapNode_cell parent
  have hRootCell : F.cell root = p.rootCell := Except.ok.inj
    ((Canonical.cellAt_of_frame_node p.reduced root).symm.trans (by simpa only [hRoot] using p.restored_root))
  have hSearch : findParent p.initial p.root = .ok (Frame.ref parent) := by
    rw [findParent_eq_of_columns (fun c hc =>
      build_changed_last_preserves_prefix p.initial_build p.reduced_build (hc.trans_lt p.root_before_last))]
    simpa only [hRoot] using (Executable.findParent_ref_iff hSourceNormal.toOrdered root parent).mpr hParent
  obtain ⟨reference, cell, hBelow, hRead, hSelectorLow, hCases⟩ := p.blocks_highest_classification_of_run hLast hRun
  have hRaw : RawRefEdge start reference (Frame.ref parent) := by
    rcases hCases with ⟨oldParent, hOldSearch, _, hEdge, _⟩ | ⟨hNone, _⟩
    · have he : Frame.ref oldParent = Frame.ref parent := Except.ok.inj (hOldSearch.symm.trans hSearch)
      exact he ▸ hEdge
    · rw [hSearch] at hNone
      cases hNone
  obtain ⟨selected, hSelectedRef, hSelectedCell⟩ := Canonical.frame_node_of_cellAt hRead
  have hRawTyped : G.rawParent selected = some original := hRaw.rawParent hSelectedRef hOriginalRef
  have hLastBound : start.size - 1 < start.size := by omega
  have hSelectedColumn : selected.1.val = start.size - 1 :=
    (congrArg Ref.column hSelectedRef).trans
      (below_result (Array.getElem?_eq_getElem hLastBound) hBelow).1
  obtain ⟨valueRef, valueCell, hValueBelow, hValueRead, _, hValue⟩ := p.blocks_highest_reference_value hLast hRun
  have hValueRef : valueRef = reference := Except.ok.inj (hValueBelow.symm.trans hBelow)
  have hValueCell : valueCell = cell := Except.ok.inj ((hValueRef ▸ hValueRead).symm.trans hRead)
  have hSelectorValue : G.value selected = F.value root :=
    (congrArg Cell.value hSelectedCell).trans (hValueCell ▸ hValue |>.trans (congrArg Cell.value hRootCell).symm)
  have hSelectedReal : Real selected := Frame.real_of_value_pos hNormal.toOrdered
    (hSelectorValue ▸ (P_value hSourceNormal.toOrdered hParent).1.trans
      (P_value hSourceNormal.toOrdered hParent).2)
  have hSelectedParent : G.P selected = some original :=
    (hNormal.rawParent_eq_P hSelectedReal).symm.trans hRawTyped
  let high := max cut (G.height selected)
  have hHigher : cut ≤ high := le_max_left _ _
  have hHighBelow : high < p.lastTop.row := max_lt hHigh
    ((congrArg Cell.row hSelectedCell).trans_lt hSelectorLow)
  have hSelectedFront : frontierAt hNormal.toOrdered high (hCut.trans hHigher) selected.1 = selected := by
    apply frontierAt_eq_of_upper_barrier hNormal.toOrdered (hCut.trans hHigher) (le_max_right _ _)
    intro upper hUpper
    have hUpperRead : Canonical.cellAt start ⟨reference.column, reference.index + 1⟩ = .ok (G.cell upper) := by
      have hr : Frame.ref upper = ⟨reference.column, reference.index + 1⟩ := congrArg₂ Ref.mk
        ((congrArg Fin.val (upper_spec hUpper).1).trans (congrArg Ref.column hSelectedRef))
        ((upper_spec hUpper).2.trans (congrArg (· + 1) (congrArg Ref.index hSelectedRef)))
      rw [← hr]
      exact Canonical.cellAt_of_frame_node start upper
    exact hHighBelow.trans_le (below_parent_upper_bound_at hBelow hUpperRead)
  have hParentFront : frontierAt hNormal.toOrdered cut hCut original.1 = original := by
    apply frontierAt_eq_of_upper_barrier hNormal.toOrdered hCut
    · exact (ready.base_preserved.mapNode_height parent).trans_le
        ((P_height_le hSourceNormal.toOrdered hParent).trans hLow)
    · intro upper hUpper
      have hUpperMap := ready.base_preserved.mapNode_upper_eq parent
      change G.upper original = (F.upper parent).map ready.base_preserved.mapNode at hUpperMap
      rw [hUpper] at hUpperMap
      cases hOldUpper : F.upper parent with
      | none => rw [hOldUpper] at hUpperMap; cases hUpperMap
      | some oldUpper =>
        have hOldUpperEq : ready.base_preserved.mapNode oldUpper = upper :=
          Option.some.inj (by simpa only [hOldUpper, Option.map_some] using hUpperMap.symm)
        obtain ⟨rootUpper, hRootUpper⟩ := hSourceNormal.upper_of_parent hParent
        have hBarrier := (p.reduced_badRoot_upper_bound hLast hRoot hRootUpper).trans
          (father_upper_bound_nodes hSourceNormal hParent hRootUpper hOldUpper)
        exact (hHigh.trans_le hBarrier).trans_eq
          ((ready.base_preserved.mapNode_height oldUpper).symm.trans (congrArg G.height hOldUpperEq))
  obtain ⟨z, path, edge, barrier⟩ := build_cut_parent_last_record hBuild hWidth
    hSelectedParent hCut hHigher hSelectedFront hParentFront
  have hColumnEq : selected.1 = (⟨start.size - 1, by
      change start.size - 1 < start.size; omega⟩ : Fin G.width) := Fin.ext hSelectedColumn
  exact ⟨original, z, hOriginalRef, hOriginalCell, by simpa only [hColumnEq] using path,
    edge, hSelectorValue.symm.trans_le barrier⟩

theorem EffectiveCopyOccurrence.candidate_highest_root_records
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block startCopies : Nat} {start result : Mountain} {references : List Ref}
    {source parent candidate candidateParent : (Frame.ofMountain p.reduced).Node}
    (copy : EffectiveCopyOccurrence p block start references source result)
    (hLast : 1 < last) (hValid : MountainValid result)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hKnown : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    (hParent : (Frame.ofMountain p.reduced).P source = some parent)
    (hFixed : parent.1.val < p.root.column)
    (hCandidate : (Frame.ofMountain p.reduced).Q source = some candidate)
    (hRoot : Frame.ref candidate = p.root)
    (hCandidateParent : (Frame.ofMountain p.reduced).P candidate = some candidateParent)
    (hSourceLow : (Frame.ofMountain p.reduced).height source < p.lastTop.row) :
    ∃ actualSource actualCandidate originalParent z : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      Frame.ref originalParent = Frame.ref candidateParent ∧
      (Frame.ofMountain result).cell originalParent = (Frame.ofMountain p.reduced).cell candidateParent ∧
      ParentPath (Frame.ofMountain result) actualCandidate z ∧
      (Frame.ofMountain result).P z = some originalParent ∧
      (Frame.ofMountain p.reduced).value candidate ≤ (Frame.ofMountain result).value z := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index := by
    intro h
    obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
    have he : marker = Frame.ref source := congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
    exact p.fixed_parent_not_marked hParent hFixed (he ▸ hm)
  have hNoPremature := (copy.state.column_data_parent_inputs hLast source.1.isLt copy.data).1
  obtain ⟨copied, hCopy, hShape⟩ := copy.read.nonmarker_copy_execution hNoPremature hUnmarked
  obtain ⟨actualSource, actualCandidate, hSourceRef, _, hQ, _, hColumn, hCut, hFront⟩ :=
    copy.candidate_frontier_all_columns hValid hReal hCopy hShape hCandidate
  have hPreserved : PreservesColumns start result := copy.state.start_preserved.trans
    ((PreservesColumns.push copy.before copy.column).trans copy.preserved)
  have hStartNormal := p.blocks_normal_of_left_recognition hLast hStartRun hPreserved hValid.toOrdered hKnown
  have hWidth : 0 < start.size := by have := copy.state.start_size; omega
  have hRootColumn : candidate.1.val = p.root.column := congrArg Ref.column hRoot
  obtain ⟨hLow, _⟩ := copy.root_candidate_range hLast hCandidate hRootColumn
  obtain ⟨original, z, hOriginalRef, hOriginalCell, hPath, hLastEdge, hBarrier⟩ :=
    p.blocks_highest_root_records_at_cut hLast hStartRun hPreserved hValid.toOrdered hKnown
      hRoot hCandidateParent copy.state.start_valid hWidth hCut hLow (copy.row_lt_lastTop hLast hSourceLow)
  let boundary : (Frame.ofMountain start).Node :=
    frontierAt copy.state.start_valid.toOrdered copy.read.outputCell.row hCut
      ⟨start.size - 1, by change start.size - 1 < start.size; omega⟩
  have hBoundaryColumn : boundary.1.val = start.size - 1 :=
    congrArg Fin.val (frontierAt_spec copy.state.start_valid.toOrdered hCut _).1
  have hBoundaryFront : frontierAt copy.state.start_valid.toOrdered copy.read.outputCell.row hCut
      boundary.1 = boundary := by
    rw [(frontierAt_spec copy.state.start_valid.toOrdered hCut _).1]
  have hExpected := frontierAt_of_same_column copy.state.start_valid.toOrdered hValid.toOrdered
    hCut hBoundaryFront (hPreserved.mapNode_ref boundary) (hPreserved _ boundary.1.isLt)
  have hActualColumn : actualCandidate.1.val = p.root.column +
      block * (p.reduced.size - 1 - p.root.column) := by
    simpa only [hRootColumn, lt_self_iff_false, if_false] using hColumn
  have hc : (hPreserved.mapNode boundary).1 = actualCandidate.1 := by
    apply Fin.ext
    rw [hPreserved.mapNode_column, hBoundaryColumn, hActualColumn]
    have hSize := copy.state.start_size
    omega
  have he : hPreserved.mapNode boundary = actualCandidate := by
    rw [hc, hFront] at hExpected
    exact hExpected.symm
  have hMapped := hPreserved.mapNode_parentPath hStartNormal.toOrdered hValid.toOrdered hPath
  change ParentPath G (hPreserved.mapNode boundary) (hPreserved.mapNode z) at hMapped
  rw [he] at hMapped
  exact ⟨actualSource, actualCandidate, hPreserved.mapNode original, hPreserved.mapNode z,
    hSourceRef, hQ, (hPreserved.mapNode_ref original).trans hOriginalRef,
    (hPreserved.mapNode_cell original).trans hOriginalCell, hMapped,
    hPreserved.mapNode_P hStartNormal.toOrdered hValid.toOrdered hLastEdge,
    hBarrier.trans_eq (congrArg Cell.value (hPreserved.mapNode_cell z)).symm⟩

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent result)

theorem recognize_highest_root_candidate_low
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies startCopies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hRoot : Frame.ref packet.candidate = p.root)
    (hSourceLow : (Frame.ofMountain p.reduced).height sourceU < p.lastTop.row)
    (hKnown : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hPreserved := p.expandDiagram_reduced_preserved hLast hCopies hRun
  have hRootColumn : packet.candidate.1.val = p.root.column := congrArg Ref.column hRoot
  have hZLe : packet.blocker.1.val ≤ p.root.column :=
    (packet.source_path.column_le hNormal.toOrdered).trans_eq hRootColumn
  have hParentFixed : sourceParent.1.val < p.root.column :=
    (Frame.P_column_lt hNormal.toOrdered packet.source_last_parent).trans_le hZLe
  have hUValue : 1 < F.value sourceU := by
    have hp := P_value hNormal.toOrdered packet.source_parent
    dsimp [F]
    omega
  have hCandidateLarge : 1 < F.value packet.candidate :=
    (hUValue.trans_le packet.source_value).trans_le (packet.source_path.value_le hNormal.toOrdered)
  obtain ⟨qParent, hQParent⟩ := hNormal.parent_exists hCandidateLarge
  obtain ⟨u, q, original, z, hURef, hQ, hOriginalRef, _, hPath, hLastEdge, hBarrier⟩ :=
    packet.pair.uCopy.candidate_highest_root_records hLast hValid hStartRun hKnown
      packet.source_parent hParentFixed packet.source_candidate hRoot hQParent hSourceLow
  have heU : u = packet.pair.u := Executable.ref_injective G (hURef.trans packet.pair.u_ref.symm)
  subst u
  have heOriginal : original = hPreserved.mapNode qParent := Executable.ref_injective G
    (hOriginalRef.trans (hPreserved.mapNode_ref qParent).symm)
  rw [heOriginal] at hLastEdge
  have hParentRef : Frame.ref packet.pair.parent = Frame.ref sourceParent := by
    rcases packet.pair.parent_origin with ⟨_, hRef, _⟩ | ⟨hRootParent, _⟩ | ⟨hRight, _⟩
    · exact hRef
    · exact False.elim (ne_of_lt hParentFixed hRootParent)
    · exact False.elim (not_lt_of_ge hParentFixed.le hRight)
  have heParent : hPreserved.mapNode sourceParent = packet.pair.parent :=
    Executable.ref_injective G ((hPreserved.mapNode_ref sourceParent).trans hParentRef.symm)
  have hSmall := ((expandDiagram_equations hLegal hRun).1.rawParent_value_lt
    hValid packet.pair.u_real packet.pair.u_parent).2
  by_cases hSame : packet.candidate = packet.blocker
  · have hRootP : F.P packet.candidate = some sourceParent := hSame ▸ packet.source_last_parent
    have heQParent : qParent = sourceParent := Option.some.inj (hQParent.symm.trans hRootP)
    rw [heQParent, heParent] at hLastEdge
    have hValue : G.value packet.pair.u = F.value sourceU :=
      (congrArg Cell.value packet.pair.u_cell).trans
        (packet.pair.uCopy.value_of_fixed_parent_expansion hLast hLegal hRun packet.source_parent hParentFixed)
    have hUBarrier : G.value packet.pair.u ≤ G.value z := by
      rw [hValue]
      exact packet.source_value.trans (hSame ▸ hBarrier)
    exact Frame.P_of_record_barrier hValid.toOrdered hQ hPath hLastEdge hUBarrier hSmall
  · have hTail : ParentPath F qParent packet.blocker := by
      obtain ⟨next, edge, tail⟩ := path_first packet.source_path hSame
      have he : next = qParent := Option.some.inj (edge.symm.trans hQParent)
      exact he ▸ tail
    have hZRef : Frame.ref packet.pair.z = Frame.ref packet.blocker := by
      rcases packet.pair.z_origin with ⟨_, hRef, _⟩ | ⟨hRight, _⟩
      · exact hRef
      · exact False.elim (not_lt_of_ge hZLe hRight)
    have heZ : hPreserved.mapNode packet.blocker = packet.pair.z :=
      Executable.ref_injective G ((hPreserved.mapNode_ref packet.blocker).trans hZRef.symm)
    have hTailMapped := hPreserved.mapNode_parentPath hNormal.toOrdered hValid.toOrdered hTail
    rw [heZ] at hTailMapped
    have hLastP := hPreserved.mapNode_P hNormal.toOrdered hValid.toOrdered packet.source_last_parent
    rw [heZ, heParent] at hLastP
    exact Frame.P_of_record_barrier hValid.toOrdered hQ
      (hPath.trans (.cons hLastEdge hTailMapped)) hLastP
      (packet.fixed_parent_barrier hLast hLegal hRun hParentFixed) hSmall

end AnySourceBlockerPacket

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_highest_root_records_at_cut
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_highest_root_records
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.recognize_highest_root_candidate_low
