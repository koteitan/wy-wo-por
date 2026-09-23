/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualLowRootCandidateRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootCandidateRange
import OmegaY.Expansion.RecognizedBoundaryDepth
import OmegaY.Expansion.ActualLowRootCorrection

/-!
# Root-candidate record paths below the bad root

The actual completed-block boundary is projected to the current copied cut
inside the source root interval. Its path reaches the preserved source
candidate. Numerical recognition is assumed only in the already completed
block prefix; the current copied column is not assumed canonical.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

theorem Preparation.blocks_low_root_frontier_path_of_left_recognition
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {start ambient : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hPreserved : PreservesColumns start ambient) (hAmbient : (Frame.ofMountain ambient).Ordered)
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent)
    {root rootUpper : (Frame.ofMountain p.reduced).Node}
    (hRootReal : Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.reduced).upper root = some rootUpper)
    (hStartValid : MountainValid start) (hWidth : 0 < start.size)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hLow : (Frame.ofMountain p.reduced).height root ≤ cut)
    (hHigh : cut < (Frame.ofMountain p.reduced).height rootUpper) :
    ∃ originalRoot : (Frame.ofMountain start).Node,
      Frame.ref originalRoot = Frame.ref root ∧
      (Frame.ofMountain start).cell originalRoot = (Frame.ofMountain p.reduced).cell root ∧
      ParentPath (Frame.ofMountain start)
        (frontierAt hStartValid.toOrdered cut hCut ⟨start.size - 1, by
          change start.size - 1 < start.size; omega⟩) originalRoot := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain start
  obtain ⟨values, _, hBuild⟩ := p.blocks_reconstruct_of_left_recognition
    hLast hRun hPreserved hAmbient hKnown
  have hNormal := build_normal_of_success hBuild
  obtain ⟨output, hOutput, hReady⟩ := p.blocks_total hLast copies
  have he : output = start := Except.ok.inj (hOutput.symm.trans hRun)
  subst output
  have hRootLeft : root.1.val < front.length := hRootColumn ▸ p.root_before_last
  have hUpperLeft : rootUpper.1.val < front.length :=
    (congrArg Fin.val (upper_spec hRootUpper).1).trans_lt hRootLeft
  have hInitialRoot : Canonical.cellAt p.initial (Frame.ref root) = .ok (F.cell root) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hRootLeft).trans
      (Canonical.cellAt_of_frame_node p.reduced root)
  have hInitialUpper : Canonical.cellAt p.initial (Frame.ref rootUpper) = .ok (F.cell rootUpper) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hUpperLeft).trans
      (Canonical.cellAt_of_frame_node p.reduced rootUpper)
  obtain ⟨oldRoot, hOldRootRef, hOldRootCell⟩ := Canonical.frame_node_of_cellAt hInitialRoot
  obtain ⟨oldUpper, hOldUpperRef, hOldUpperCell⟩ := Canonical.frame_node_of_cellAt hInitialUpper
  have hOldReal : Real oldRoot := by
    change 0 < oldRoot.2.val
    have hi : oldRoot.2.val = root.2.val := congrArg Ref.index hOldRootRef
    rw [hi]
    exact hRootReal
  have hOldColumn : oldRoot.1.val = p.root.column :=
    (congrArg Ref.column hOldRootRef).trans hRootColumn
  have hOldBefore : oldRoot.2.val < p.root.index := by
    have hi : oldRoot.2.val = root.2.val := congrArg Ref.index hOldRootRef
    rw [hi]
    exact hBefore
  have hOldUpper : (Frame.ofMountain p.initial).upper oldRoot = some oldUpper := by
    apply Frame.upper_of_refs hOldRootRef
    rw [hOldUpperRef]
    exact congrArg₂ Ref.mk (congrArg Fin.val (upper_spec hRootUpper).1) (upper_spec hRootUpper).2
  obtain ⟨data⟩ := p.blocks_low_boundary_event_depth hLast hRun
    hOldReal hOldColumn hOldBefore hOldUpper
  obtain ⟨event, hEvent, hEventCut, _, hEventFront⟩ := event_floor_at_cut hNormal.toOrdered hCut
  have hOrder : event ≤ data.event := by
    by_contra hNot
    have hRows := G.eventCut_monotone (show data.event + 1 ≤ event by omega)
    rw [data.next_cut] at hRows
    have hCap : (Frame.ofMountain p.initial).height oldUpper = F.height rootUpper :=
      congrArg Cell.row hOldUpperCell
    exact (not_lt_of_ge (hCap ▸ hRows.trans hEventCut)) hHigh
  have hRawPath := p.blocks_low_selected_path hLast hRun hOldReal hOldColumn hOldBefore
    hOldUpper data.selected_below
  have hPath : ParentPath G data.selected data.originalRoot :=
    hRawPath.toParentPath hNormal.toOrdered (bound := start.size)
      (fun _ _ hReal => hNormal.rawParent_eq_P hReal) rfl data.root_reference
      (data.selected_frontier ▸ (eventFrontier_spec hNormal.toOrdered data.event data.selected.1).2.1)
      data.selected.1.isLt
  have hProjected := build_parent_path_event_projection hBuild hWidth hOrder
    data.event_before_last.le data.selected_frontier hPath
  let original := hReady.base_preserved.mapNode root
  have hOriginalRef : Frame.ref original = Frame.ref root := hReady.base_preserved.mapNode_ref root
  have hSame : data.originalRoot = original := Executable.ref_injective G
    (data.root_reference.trans (hOldRootRef.trans hOriginalRef.symm))
  have hFront : frontierAt hNormal.toOrdered cut hCut original.1 = original := by
    apply frontierAt_eq_of_upper_barrier hNormal.toOrdered hCut
    · exact (hReady.base_preserved.mapNode_height root).trans_le hLow
    · intro upper hUpper
      have hMapped := hReady.base_preserved.mapNode_upper hRootUpper
      have he : upper = hReady.base_preserved.mapNode rootUpper := Option.some.inj (hUpper.symm.trans hMapped)
      exact hHigh.trans_eq ((hReady.base_preserved.mapNode_height rootUpper).symm.trans
        (congrArg G.height he).symm)
  rw [hEventFront, hEventFront, hSame, hFront] at hProjected
  have hSelectedColumn : data.selected.1 = (⟨start.size - 1, by
      change start.size - 1 < start.size; omega⟩ : Fin G.width) :=
    Fin.ext data.selected_column
  refine ⟨original, hOriginalRef, hReady.base_preserved.mapNode_cell root, ?_⟩
  simpa only [hSelectedColumn] using hProjected

theorem EffectiveCopyOccurrence.candidate_low_root_path
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block startCopies : Nat} {start result : Mountain} {references : List Ref}
    {source parent candidate : (Frame.ofMountain p.reduced).Node}
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
    (hRoot : candidate.1.val = p.root.column)
    (hBefore : candidate.2.val < p.root.index) :
    ∃ actualSource actualCandidate originalCandidate : (Frame.ofMountain result).Node,
      Frame.ref actualSource = copy.outputRef ∧
      (Frame.ofMountain result).Q actualSource = some actualCandidate ∧
      Frame.ref originalCandidate = Frame.ref candidate ∧
      (Frame.ofMountain result).cell originalCandidate = (Frame.ofMountain p.reduced).cell candidate ∧
      ParentPath (Frame.ofMountain result) actualCandidate originalCandidate := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hCandidateReal := Frame.Q_real hNormal.toOrdered hReal hCandidate
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
  obtain ⟨upper, hUpper⟩ := p.root_upper_of_before_badRoot hRoot hBefore
  obtain ⟨hLow, hHigh⟩ := copy.root_candidate_range hLast hCandidate hRoot
  obtain ⟨original, hOriginalRef, hOriginalCell, hPath⟩ :=
    p.blocks_low_root_frontier_path_of_left_recognition hLast hStartRun hPreserved hValid.toOrdered
      hKnown hCandidateReal hRoot hBefore hUpper copy.state.start_valid hWidth hCut hLow (hHigh _ hUpper)
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
    simpa only [hRoot, lt_self_iff_false, if_false] using hColumn
  have hc : (hPreserved.mapNode boundary).1 = actualCandidate.1 := by
    apply Fin.ext
    rw [hPreserved.mapNode_column, hBoundaryColumn, hActualColumn]
    have hSize := copy.state.start_size
    omega
  have he : hPreserved.mapNode boundary = actualCandidate := by
    rw [hc, hFront] at hExpected
    exact hExpected.symm
  have hMapped := hPreserved.mapNode_parentPath hStartNormal.toOrdered hValid.toOrdered hPath
  change ParentPath G (hPreserved.mapNode boundary) (hPreserved.mapNode original) at hMapped
  rw [he] at hMapped
  exact ⟨actualSource, actualCandidate, hPreserved.mapNode original, hSourceRef, hQ,
    (hPreserved.mapNode_ref original).trans hOriginalRef,
    (hPreserved.mapNode_cell original).trans hOriginalCell, hMapped⟩

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references sourceU sourceParent result)

theorem recognize_low_root_candidate
    (hLast : 1 < last) (hLegal : Canonical.Legal (front ++ [last]))
    {copies startCopies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hRoot : packet.candidate.1.val = p.root.column)
    (hBefore : packet.candidate.2.val < p.root.index)
    (hKnown : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hPreserved := p.expandDiagram_reduced_preserved hLast hCopies hRun
  have hZLe : packet.blocker.1.val ≤ p.root.column :=
    (packet.source_path.column_le hNormal.toOrdered).trans_eq hRoot
  have hParentFixed : sourceParent.1.val < p.root.column :=
    (Frame.P_column_lt hNormal.toOrdered packet.source_last_parent).trans_le hZLe
  obtain ⟨u, q, original, hURef, hQ, hOriginalRef, _, hQPath⟩ :=
    packet.pair.uCopy.candidate_low_root_path hLast hValid hStartRun hKnown
      packet.source_parent hParentFixed packet.source_candidate hRoot hBefore
  have heU : u = packet.pair.u := Executable.ref_injective G (hURef.trans packet.pair.u_ref.symm)
  subst u
  have heOriginal : original = hPreserved.mapNode packet.candidate := Executable.ref_injective G
    (hOriginalRef.trans (hPreserved.mapNode_ref packet.candidate).symm)
  rw [heOriginal] at hQPath
  have hZRef : Frame.ref packet.pair.z = Frame.ref packet.blocker := by
    rcases packet.pair.z_origin with ⟨_, hRef, _⟩ | ⟨hRight, _⟩
    · exact hRef
    · exact False.elim (not_lt_of_ge hZLe hRight)
  have hParentRef : Frame.ref packet.pair.parent = Frame.ref sourceParent := by
    rcases packet.pair.parent_origin with ⟨_, hRef, _⟩ | ⟨hRootParent, _⟩ | ⟨hRight, _⟩
    · exact hRef
    · exact False.elim (ne_of_lt hParentFixed hRootParent)
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
  exact Frame.P_of_record_barrier hValid.toOrdered hQ (hQPath.trans hPath) hLastParent hBarrier hSmall

end AnySourceBlockerPacket

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_low_root_frontier_path_of_left_recognition
#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.candidate_low_root_path
#print axioms OmegaY.Expansion.AnySourceBlockerPacket.recognize_low_root_candidate
