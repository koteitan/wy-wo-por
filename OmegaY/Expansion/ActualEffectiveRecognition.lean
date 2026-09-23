/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualBlockerRecognition
import OmegaY.Expansion.ActualMarkedEffectiveSearch
import OmegaY.Expansion.ActualStationaryMarkerCandidate

/-!
# Every effective last-blocker branch with a copied common parent

Unmarked nodes and stationary markers use the source candidate's actual
effective occurrence and its recorded path. A raised marker endpoint has
an actual immediate hit at the effective source parent instead. This
classification is internal; no incorrect uniform Q-copy identity is used.
The generic target blocker comparison is still a premise, and its depth
word transport remains separate from the search recognition proved here.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

namespace SourceBlockerCopyPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {sourceU sourceParent : (Frame.ofMountain p.reduced).Node}
  (packet : SourceBlockerCopyPacket p block start references sourceU sourceParent result)

theorem recognize_of_barrier (hLast : 1 < last)
    (hValid : MountainValid result) (hSums : MountainSums result)
    (hLeft : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < packet.pair.u.1.val → Real node →
      (Frame.ofMountain result).rawParent node = some father →
      (Frame.ofMountain result).P node = some father)
    (hParentRight : p.root.column < sourceParent.1.val)
    (hBarrier : (Frame.ofMountain result).value packet.pair.u ≤
      (Frame.ofMountain result).value packet.pair.z) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  by_cases hMarkedIndex : sourceU.2.val ∈ (p.marked[sourceU.1.val]?.getD []).map Ref.index
  · have hMarked : BucketMem p.marked sourceU.1.val (Frame.ref sourceU) := by
      obtain ⟨marker, hm, hIndex⟩ := List.mem_map.mp hMarkedIndex
      have hColumn := (p.marker_iff.mp hm).1
      have hRef : marker = Frame.ref sourceU := by
        cases marker
        simp only [Frame.ref, Ref.mk.injEq]
        exact ⟨hColumn, hIndex⟩
      exact hRef ▸ hm
    rcases eq_or_lt_of_le packet.pair.uCopy.read.source_row_le_output with hStationary | hRaised
    · obtain ⟨actual, candidate, hActualRef, hCandidateRef, hQ, _⟩ :=
        packet.pair.uCopy.candidate_eq_stationary_marker hValid hMarked packet.candidateCopy
          packet.source_parent packet.source_candidate hParentRight hStationary.symm
      have he : actual = packet.pair.u := Executable.ref_injective _
        (hActualRef.trans packet.pair.u_ref.symm)
      subst actual
      exact packet.recognize_of_candidate_barrier hValid hSums hLeft hQ hCandidateRef hBarrier
    · have hSearch := packet.pair.uCopy.raised_marker_search hLast hValid hMarked packet.pair.parentCopy
        packet.source_parent hParentRight hRaised
      apply (Executable.findParent_ref_iff hValid.toOrdered packet.pair.u packet.pair.parent).mp
      simpa only [packet.pair.u_ref, packet.pair.parent_ref] using hSearch.2
  · exact packet.recognize_of_nonmarker_barrier hLast hValid hSums hLeft hMarkedIndex hParentRight hBarrier

theorem comparison_event (hLast : 1 < last)
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
  exact ⟨event, hEvent, hCut, fun hWord => packet.recognize_of_barrier hLast
    (expandDiagram_valid_of_success hLegal hRun) (expandDiagram_equations hLegal hRun).1
    hLeft hParentRight (hComparison.mp hWord)⟩

end SourceBlockerCopyPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.recognize_of_barrier
#print axioms OmegaY.Expansion.SourceBlockerCopyPacket.comparison_event
