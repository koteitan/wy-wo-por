/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualBlockerRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualBlockerDepthWords
import OmegaY.Expansion.ActualStationaryEffectiveCandidate

/-!
# Actual copied candidate records and their remaining numerical barrier

For every nonmarker source with its parent strictly right of the root,
the new Q is obtained from execution. The recorded raw path gives P records using only
strictly earlier columns. Thus the sole remaining value premise in this
recognition step is the comparison with the actual last blocker. This
module does not assert that the comparison transports from the source.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem RawRefPath.toParentPath_of_recognition {mountain : Mountain}
    (hF : (Frame.ofMountain mountain).Ordered) {bound : Nat}
    (hKnown : ∀ (node parent : (Frame.ofMountain mountain).Node),
      node.1.val < bound → Real node →
      (Frame.ofMountain mountain).rawParent node = some parent →
      (Frame.ofMountain mountain).P node = some parent)
    {child parent : Ref} (path : RawRefPath mountain child parent)
    {u p : (Frame.ofMountain mountain).Node} (hU : Frame.ref u = child)
    (hP : Frame.ref p = parent) (hReal : Real u) (hLeft : u.1.val < bound) :
    ParentPath (Frame.ofMountain mountain) u p := by
  induction path generalizing u with
  | refl ref =>
      have he : u = p := Executable.ref_injective _ (hU.trans hP.symm)
      subst u
      exact .refl _
  | @cons child next parent edge tail ih =>
      have edgeRead := edge
      obtain ⟨_, _, _, _, _, _, hRead⟩ := edgeRead
      obtain ⟨q, hQRef, _⟩ := Canonical.frame_node_of_cellAt hRead
      have hNext := hKnown u q hLeft hReal (edge.rawParent hU hQRef)
      exact .cons hNext (ih hQRef hP
        (Frame.real_of_value_pos hF (Frame.P_value hF hNext).1)
        ((Frame.P_column_lt hF hNext).trans hLeft))

namespace SourceBlockerCopyPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : SourceBlockerCopyPacket p block start references sourceU sourceParent result)

/-- Once the actual Q identity is established, the stored path is expanded
to numerical records in strictly earlier columns only. -/
theorem recognize_of_candidate_barrier
    (hValid : MountainValid result) (hSums : MountainSums result)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
    {candidate : (Frame.ofMountain result).Node}
    (hQ : (Frame.ofMountain result).Q packet.pair.u = some candidate)
    (hCandidateRef : Frame.ref candidate = packet.candidateCopy.outputRef)
    (hBarrier : (Frame.ofMountain result).value packet.pair.u ≤
      (Frame.ofMountain result).value packet.pair.z) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  have hQReal := Frame.Q_real hValid.toOrdered packet.pair.u_real hQ
  have hQLeft := Frame.Q_column_lt hValid.toOrdered hQ
  have path := packet.copied_record_path.toParentPath_of_recognition hValid.toOrdered hLeft
    hCandidateRef packet.pair.z_ref hQReal hQLeft
  have hZLeft := (path.column_le hValid.toOrdered).trans_lt hQLeft
  have hZP := hLeft packet.pair.z packet.pair.parent hZLeft packet.pair.z_real packet.pair.z_parent
  obtain ⟨parent, hParent, _, _, hSmall, _⟩ :=
    hSums.rawParent_upper hValid packet.pair.u_real packet.pair.u_upper
  have he : parent = packet.pair.parent := Option.some.inj (hParent.symm.trans packet.pair.u_parent)
  subst parent
  exact Frame.P_of_record_barrier hValid.toOrdered hQ path hZP hBarrier hSmall

theorem recognize_of_high_barrier (hLast : 1 < last)
    (hValid : MountainValid result) (hSums : MountainSums result)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height packet.candidate)
    (hBarrier : (Frame.ofMountain result).value packet.pair.u ≤
      (Frame.ofMountain result).value packet.pair.z) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  have hNormal := build_normal_of_success p.reduced_build
  have hSourceHigh := hHigh.trans (Frame.Q_height_le hNormal.toOrdered packet.source_candidate)
  have hUnmarked := packet.pair.uCopy.state.high_source_not_marked hLast sourceU.1.isLt
    packet.pair.uCopy.data packet.pair.uCopy.read.source_at hSourceHigh
  have hMoved := packet.candidateCopy.state.next_lower.le
  obtain ⟨actual, candidate, hActualRef, hCandidateRef, hQ, _⟩ :=
    packet.pair.uCopy.candidate_eq_high hLast hValid hUnmarked packet.candidateCopy
      packet.source_candidate hMoved hHigh
  have he : actual = packet.pair.u := Executable.ref_injective _ (hActualRef.trans packet.pair.u_ref.symm)
  subst actual
  exact packet.recognize_of_candidate_barrier hValid hSums hLeft hQ hCandidateRef hBarrier

theorem recognize_of_raised_barrier (hLast : 1 < last)
    (hValid : MountainValid result) (hSums : MountainSums result)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
    (hUnmarked : sourceU.2.val ∉ (p.marked[sourceU.1.val]?.getD []).map Ref.index)
    (hParentRight : p.root.column < sourceParent.1.val)
    (hRaised : (Frame.ofMountain p.reduced).height sourceU < packet.pair.uCopy.read.outputCell.row)
    (hBarrier : (Frame.ofMountain result).value packet.pair.u ≤
      (Frame.ofMountain result).value packet.pair.z) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  obtain ⟨actual, candidate, hActualRef, hCandidateRef, hQ, _⟩ :=
    packet.pair.uCopy.candidate_eq_raised hLast hValid hUnmarked packet.candidateCopy
      packet.source_parent packet.source_candidate hParentRight hRaised
  have he : actual = packet.pair.u := Executable.ref_injective _ (hActualRef.trans packet.pair.u_ref.symm)
  subst actual
  exact packet.recognize_of_candidate_barrier hValid hSums hLeft hQ hCandidateRef hBarrier

/-- The current node and its Q candidate may be stationary or raised,
independently. Execution identifies the correct new Q in every case. -/
theorem recognize_of_nonmarker_barrier (hLast : 1 < last)
    (hValid : MountainValid result) (hSums : MountainSums result)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
    (hUnmarked : sourceU.2.val ∉ (p.marked[sourceU.1.val]?.getD []).map Ref.index)
    (hParentRight : p.root.column < sourceParent.1.val)
    (hBarrier : (Frame.ofMountain result).value packet.pair.u ≤
      (Frame.ofMountain result).value packet.pair.z) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  obtain ⟨actual, candidate, hActualRef, hCandidateRef, hQ, _⟩ :=
    packet.pair.uCopy.candidate_eq_nonmarker hLast hValid hUnmarked packet.candidateCopy
      packet.source_parent packet.source_candidate hParentRight
  have he : actual = packet.pair.u := Executable.ref_injective _ (hActualRef.trans packet.pair.u_ref.symm)
  subst actual
  exact packet.recognize_of_candidate_barrier hValid hSums hLeft hQ hCandidateRef hBarrier

/-- In the high-Q branch, all search and path premises are discharged.
The actual target depth-word inequality remains visible as the sufficient
condition at the actual comparison event. -/
theorem high_comparison_event (hLast : 1 < last)
    {input : List Nat} (hLegal : Canonical.Legal input) {copies : Nat}
    (hRun : expandDiagram input copies = .ok result)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
    (hHigher : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height packet.candidate) :
    let F := Frame.ofMountain result
    let hValid := expandDiagram_valid_of_success hLegal hRun
    let hWidth := (Nat.zero_le packet.pair.u.1.val).trans_lt packet.pair.u.1.isLt
    let forests := F.frontierForests (bottomCandidateMap packet.pair.u.1.val)
      (eventFrontierNat hValid.toOrdered hWidth) packet.pair.u.1.val
    ∃ event, event < F.lastEvent ∧ F.eventCut (event + 1) = F.height packet.pair.uUpper ∧
      (Forests.DepthWordLe forests (event + 1) F.lastEvent packet.pair.u.1.val packet.pair.z.1.val →
        F.P packet.pair.u = some packet.pair.parent) := by
  obtain ⟨event, hEvent, hCut, hComparison⟩ := packet.target_depth_word_comparison hLegal hRun hLeft hHigher
  exact ⟨event, hEvent, hCut, fun hWord => packet.recognize_of_high_barrier hLast
    (expandDiagram_valid_of_success hLegal hRun) (expandDiagram_equations hLegal hRun).1
    hLeft hHigh (hComparison.mp hWord)⟩

/-- For all nonmarker copies with a strictly-right source parent, the
remaining sufficient condition is the depth-word inequality at the actual
common upper event. Source and target words are still distinct objects. -/
theorem nonmarker_comparison_event (hLast : 1 < last)
    {input : List Nat} (hLegal : Canonical.Legal input) {copies : Nat}
    (hRun : expandDiagram input copies = .ok result)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
    (hHigher : ∀ (node father : (Frame.ofMountain result).Node), node.1 = packet.pair.u.1 →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain result).height node →
      Real node → (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
    (hUnmarked : sourceU.2.val ∉ (p.marked[sourceU.1.val]?.getD []).map Ref.index)
    (hParentRight : p.root.column < sourceParent.1.val) :
    let F := Frame.ofMountain result
    let hValid := expandDiagram_valid_of_success hLegal hRun
    let hWidth := (Nat.zero_le packet.pair.u.1.val).trans_lt packet.pair.u.1.isLt
    let forests := F.frontierForests (bottomCandidateMap packet.pair.u.1.val)
      (eventFrontierNat hValid.toOrdered hWidth) packet.pair.u.1.val
    ∃ event, event < F.lastEvent ∧ F.eventCut (event + 1) = F.height packet.pair.uUpper ∧
      (Forests.DepthWordLe forests (event + 1) F.lastEvent packet.pair.u.1.val packet.pair.z.1.val →
        F.P packet.pair.u = some packet.pair.parent) := by
  obtain ⟨event, hEvent, hCut, hComparison⟩ := packet.target_depth_word_comparison hLegal hRun hLeft hHigher
  exact ⟨event, hEvent, hCut, fun hWord => packet.recognize_of_nonmarker_barrier hLast
    (expandDiagram_valid_of_success hLegal hRun) (expandDiagram_equations hLegal hRun).1
    hLeft hUnmarked hParentRight (hComparison.mp hWord)⟩

end SourceBlockerCopyPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.RawRefPath.toParentPath_of_recognition
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.recognize_of_high_barrier
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.recognize_of_raised_barrier
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.high_comparison_event
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.recognize_of_nonmarker_barrier
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.nonmarker_comparison_event
