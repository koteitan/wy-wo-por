/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CandidateBoundaryProjection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RecordedRootFrontierProjection
import OmegaY.Expansion.FixedCrossingRootCases
import OmegaY.Expansion.RecognizedExecutedPrefix
import OmegaY.Expansion.ActualMixedMarkerSource

/-!
# The actual copied candidate reaches the current block boundary frontier

Only the complete columns strictly left of the current column are
recognized. Their actual build permits downward projection when the
source candidate is marked and the new Q is its physical frontier rather
than its effective endpoint. The unmarked case uses the exact recorded
candidate identity. Neither case assumes a boundary path or output normality.
-/

namespace OmegaY.Expansion
open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem candidate_root_boundary_path (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent candidate root : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hFixed : parent.1.val < p.root.column)
    (hCandidate : (Frame.ofMountain p.reduced).Q execution.source = some candidate)
    (hCandidateRight : p.root.column < candidate.1.val)
    (rootPath : ParentPath (Frame.ofMountain p.reduced) candidate root)
    (hRootColumn : root.1.val = p.root.column)
    (hRef : Frame.ref node = execution.copy.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    let preserved := origin.state.start_preserved.trans
      ((PreservesColumns.push origin.before origin.column).trans origin.preserved)
    ∃ (q : (Frame.ofMountain result).Node)
        (boundary : (Frame.ofMountain origin.start).Node)
        (hCut : (1 : Row) ≤ (Frame.ofMountain result).height node),
      (Frame.ofMountain result).Q node = some q ∧
      boundary.1.val = origin.start.size - 1 ∧
      frontierAt origin.state.start_valid.toOrdered
        ((Frame.ofMountain result).height node) hCut boundary.1 = boundary ∧
      ParentPath (Frame.ofMountain result) q (preserved.mapNode boundary) := by
  let F := Frame.ofMountain p.reduced
  let E := Frame.ofMountain origin.before
  let G := Frame.ofMountain result
  have hSourceNormal := build_normal_of_success p.reduced_build
  have hLegal := build_success_legal p.initial_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  let beforePreserved := (PreservesColumns.push origin.before origin.column).trans origin.preserved
  let startPreserved := origin.state.start_preserved.trans beforePreserved
  have hKnown : ∀ (current father : G.Node), current.1.val < origin.before.size →
      Real current → G.rawParent current = some father → G.P current = some father := by
    intro current father hColumn hReal hRaw
    exact hLeft current father (hColumn.trans_eq origin.target_column) hReal hRaw
  have hBuild := origin.state.executed_prefix_reconstruct origin.history hLast
    origin.start_run beforePreserved hLegal hRun hKnown
  have hPrefixNormal := build_normal_of_success hBuild
  have hPrefixWidth : 0 < origin.before.size := by
    have := origin.state.size_eq
    have := origin.state.next_lower
    omega
  have hSourceReal := real_of_value_pos hSourceNormal.toOrdered
    ((P_value hSourceNormal.toOrdered hParent).1.trans (P_value hSourceNormal.toOrdered hParent).2)
  have hCandidateReal := Q_real hSourceNormal.toOrdered hSourceReal hCandidate
  have hSourceUnmarked : execution.source.2.val ∉
      (p.marked[execution.source.1.val]?.getD []).map Ref.index := by
    intro h
    obtain ⟨marker, hm, hi⟩ := List.mem_map.mp h
    have he : marker = Frame.ref execution.source := congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
    exact p.fixed_parent_not_marked hParent hFixed (he ▸ hm)
  have hBefore : candidate.1.val < origin.sourceColumn :=
    (Q_column_lt hSourceNormal.toOrdered hCandidate).trans_eq execution.source_column
  obtain ⟨candidateCopy⟩ := origin.state.prior_effective_occurrence origin.history hLast hCandidateRight hBefore
  obtain ⟨rootCopy, hRawPath⟩ := origin.state.recorded_effective_path_to_root_exists
    origin.history hLast origin.start_run rootPath hRootColumn hCandidateRight hBefore candidateCopy
  obtain ⟨localCandidate, hLocalCandidateRef, hLocalCandidateCell⟩ :=
    Canonical.frame_node_of_cellAt candidateCopy.output_read
  obtain ⟨localRoot, hLocalRootRef, _⟩ := Canonical.frame_node_of_cellAt rootCopy.result_read
  have hLocalCandidateReal : Real localCandidate := by
    change 0 < localCandidate.2.val
    have hIndex : localCandidate.2.val = candidateCopy.read.outputIndex := congrArg Ref.index hLocalCandidateRef
    rw [hIndex]
    exact candidateCopy.read.output_real hCandidateReal
  have hPath : ParentPath E localCandidate localRoot :=
    hRawPath.toParentPath_of_recognition hPrefixNormal.toOrdered
      (bound := origin.before.size)
      (fun _ _ _ hReal hRaw => (hPrefixNormal.rawParent_eq_P hReal).symm.trans hRaw)
      hLocalCandidateRef hLocalRootRef hLocalCandidateReal localCandidate.1.isLt
  obtain ⟨actualSource, actualQ, hActualRef, hActualCell, hQ, _, hQColumn, hOldCut, hQFront⟩ :=
    execution.copy.candidate_frontier hLast hValid hSourceUnmarked hCandidate hCandidateRight.le
  have hActualSource : actualSource = node := Executable.ref_injective G (hActualRef.trans hRef.symm)
  subst actualSource
  have hNodeRow : G.height node = execution.copy.read.outputCell.row := congrArg Cell.row hActualCell
  have hCut : (1 : Row) ≤ G.height node := hNodeRow ▸ hOldCut
  have hActualQFront : frontierAt hValid.toOrdered (G.height node) hCut actualQ.1 = actualQ := by
    simpa only [← hNodeRow] using hQFront
  have hFrontPath : ParentPath E
      (frontierAt hPrefixNormal.toOrdered (G.height node) hCut localCandidate.1)
      (frontierAt hPrefixNormal.toOrdered (G.height node) hCut localRoot.1) := by
    by_cases hMarkedIndex : candidate.2.val ∈ (p.marked[candidate.1.val]?.getD []).map Ref.index
    · obtain ⟨marker, hm, hi⟩ := List.mem_map.mp hMarkedIndex
      have he : marker = Frame.ref candidate := congrArg₂ Ref.mk (p.marker_iff.mp hm).1 hi
      have hMarked : BucketMem p.marked candidate.1.val (Frame.ref candidate) := he ▸ hm
      have hSourceCut := one_le_height hSourceNormal.toOrdered hSourceReal
      have hSourceFront : frontierAt hSourceNormal.toOrdered (F.height execution.source)
          hSourceCut candidate.1 = candidate := by
        apply frontierAt_eq_of_upper_barrier hSourceNormal.toOrdered hSourceCut
          (Q_height_le hSourceNormal.toOrdered hCandidate)
        exact fun upper hUpper => Q_upper_gt hSourceNormal.toOrdered hCandidate hUpper
      have hSameRow := candidateCopy.marked_frontier_cut_eq hMarked hSourceCut hSourceFront
      have hStationary := execution.copy.stationary_at_marker_row hLast hSourceUnmarked hMarked hSameRow
      have hBelow : G.height node ≤ E.height localCandidate := by
        rw [hNodeRow, hStationary, hSameRow]
        exact candidateCopy.read.source_row_le_output.trans_eq (congrArg Cell.row hLocalCandidateCell).symm
      exact build_parent_path_cut_projection hBuild hPrefixWidth hLocalCandidateReal hPath hCut hBelow
    · have hDistinct : candidate ≠ parent := by
        intro he
        have hc := congrArg (fun n => n.1.val) he
        omega
      obtain ⟨otherSource, otherQ, hOtherRef, hOtherQRef, hOtherQ, _⟩ :=
        execution.copy.candidate_eq_nondirect_of_unmarked_pair hLast hValid hSourceUnmarked
          (candidateCopy.extend beforePreserved) hParent hCandidate hMarkedIndex hDistinct
      have hOtherSource : otherSource = node := Executable.ref_injective G (hOtherRef.trans hRef.symm)
      subst otherSource
      have hOtherEq : otherQ = actualQ := Option.some.inj (hOtherQ.symm.trans hQ)
      subst otherQ
      have hMappedCandidate : beforePreserved.mapNode localCandidate = actualQ :=
        Executable.ref_injective G ((beforePreserved.mapNode_ref localCandidate).trans
          (hLocalCandidateRef.trans hOtherQRef.symm))
      have hLocalFront : frontierAt hPrefixNormal.toOrdered (G.height node) hCut
          localCandidate.1 = localCandidate := by
        apply frontierAt_eq_of_upper_barrier hPrefixNormal.toOrdered hCut
        · have hl := Q_height_le hValid.toOrdered hQ
          rw [← hMappedCandidate, beforePreserved.mapNode_height] at hl
          exact hl
        · intro upper hUpper
          have hu := Q_upper_gt hValid.toOrdered hQ
            (by simpa only [hMappedCandidate] using beforePreserved.mapNode_upper hUpper)
          simpa only [beforePreserved.mapNode_height] using hu
      have hRootFront := hPath.frontierAt_of_source_frontier hPrefixNormal hCut hLocalFront
      simpa only [hLocalFront, hRootFront] using hPath
  have hStartWidth : 0 < origin.start.size := by have := origin.state.start_size; omega
  let boundary : (Frame.ofMountain origin.start).Node :=
    frontierAt origin.state.start_valid.toOrdered (G.height node) hCut
      ⟨origin.start.size - 1, by change origin.start.size - 1 < origin.start.size; omega⟩
  have hBoundaryColumn : boundary.1.val = origin.start.size - 1 :=
    congrArg Fin.val (frontierAt_spec origin.state.start_valid.toOrdered hCut _).1
  have hBoundaryFront : frontierAt origin.state.start_valid.toOrdered (G.height node) hCut
      boundary.1 = boundary := by
    rw [(frontierAt_spec origin.state.start_valid.toOrdered hCut _).1]
  have hRootColumnLocal : localRoot.1.val = origin.start.size - 1 := by
    have hr : rootCopy.reference.column = origin.start.size - 1 := by
      cases rootCopy with
      | selected selected => exact selected.reference_column
      | highTail tail => exact tail.reference_column
    exact (congrArg Ref.column hLocalRootRef).trans hr
  have hBoundaryMappedFront := frontierAt_of_same_column origin.state.start_valid.toOrdered
    hPrefixNormal.toOrdered hCut hBoundaryFront (origin.state.start_preserved.mapNode_ref boundary)
    (origin.state.start_preserved _ boundary.1.isLt)
  have hBoundaryMappedColumn : (origin.state.start_preserved.mapNode boundary).1 = localRoot.1 :=
    Fin.ext ((origin.state.start_preserved.mapNode_column boundary).trans
      (hBoundaryColumn.trans hRootColumnLocal.symm))
  have hRootFrontEq : frontierAt hPrefixNormal.toOrdered (G.height node) hCut localRoot.1 =
      origin.state.start_preserved.mapNode boundary := by
    simpa only [hBoundaryMappedColumn] using hBoundaryMappedFront
  let localQ := frontierAt hPrefixNormal.toOrdered (G.height node) hCut localCandidate.1
  have hLocalQFront : frontierAt hPrefixNormal.toOrdered (G.height node) hCut localQ.1 = localQ := by
    rw [(frontierAt_spec hPrefixNormal.toOrdered hCut _).1]
  have hLocalQColumn : localQ.1 = localCandidate.1 := (frontierAt_spec hPrefixNormal.toOrdered hCut _).1
  have hQMappedFront := frontierAt_of_same_column hPrefixNormal.toOrdered hValid.toOrdered
    hCut hLocalQFront (beforePreserved.mapNode_ref localQ) (beforePreserved _ localQ.1.isLt)
  have hQMappedColumn : (beforePreserved.mapNode localQ).1 = actualQ.1 := by
    apply Fin.ext
    rw [beforePreserved.mapNode_column, congrArg Fin.val hLocalQColumn]
    exact ((congrArg Ref.column hLocalCandidateRef).trans candidateCopy.source_column).trans hQColumn.symm
  have hQMapped : beforePreserved.mapNode localQ = actualQ := by
    rw [hQMappedColumn, hActualQFront] at hQMappedFront
    exact hQMappedFront.symm
  rw [hRootFrontEq] at hFrontPath
  have hMapped := beforePreserved.mapNode_parentPath hPrefixNormal.toOrdered hValid.toOrdered hFrontPath
  change ParentPath G (beforePreserved.mapNode localQ)
    (beforePreserved.mapNode (origin.state.start_preserved.mapNode boundary)) at hMapped
  rw [hQMapped] at hMapped
  have hBoundaryRef : beforePreserved.mapNode (origin.state.start_preserved.mapNode boundary) =
      startPreserved.mapNode boundary := Executable.ref_injective G
    ((beforePreserved.mapNode_ref _).trans
      ((origin.state.start_preserved.mapNode_ref boundary).trans (startPreserved.mapNode_ref boundary).symm))
  rw [hBoundaryRef] at hMapped
  exact ⟨actualQ, boundary, hCut, hQ, hBoundaryColumn, hBoundaryFront, hMapped⟩

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ExecutedNodeCopy.candidate_root_boundary_path
