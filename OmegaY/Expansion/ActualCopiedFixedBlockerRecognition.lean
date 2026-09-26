/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualCopiedFixedBlockerRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCopiedBlockerCandidate
import OmegaY.Expansion.ActualNondirectBlocker
import OmegaY.Expansion.ActualFixedBlockerValue

/-!
# Fixed-parent recognition through a copied last blocker

The accepted source parent lies in the good part, while the source's last
rejected record remains strictly right of the root. Source marker closure
excludes a physical-marker candidate. Actual copying yields the effective
candidate and its entire record path; complete-column preservation keeps
them in the final output. Exact fixed-parent values supply the barrier.
Only recognition of strictly earlier target columns is required.
-/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem DynamicBlockState.preserved_fixed_copied_blocker_recognition
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block next : Nat} {start ambient result : Mountain} {references : List Ref}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {source parent : (Frame.ofMountain p.reduced).Node}
    (packet : AnySourceBlockerPacket p block start references source parent ambient)
    (hBefore : source.1.val < next) (preserved : PreservesColumns ambient result)
    {input : List Nat} (hLegal : Canonical.Legal input) {copies : Nat}
    (hRun : expandDiagram input copies = .ok result)
    (hFixed : parent.1.val < p.root.column)
    (hBlockerRight : p.root.column < packet.blocker.1.val)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < (packet.extend preserved).pair.u.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    (Frame.ofMountain result).rawParent (packet.extend preserved).pair.u =
      (Frame.ofMountain result).P (packet.extend preserved).pair.u := by
  let comparison := packet.extend preserved
  have hNormal := build_normal_of_success p.reduced_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hSums := (OmegaY.Expansion.expandDiagram_equations hLegal hRun).1
  have hQRight := hBlockerRight.trans_le (packet.source_path.column_le hNormal.toOrdered)
  have hQBefore := (Frame.Q_column_lt hNormal.toOrdered packet.source_candidate).trans hBefore
  obtain ⟨candidateCopy⟩ := s.prior_effective_occurrence history hLast hQRight hQBefore
  obtain ⟨zCopy, hZRefLocal, _⟩ :
      ∃ zCopy : EffectiveCopyOccurrence p block start references packet.blocker ambient,
        Frame.ref packet.pair.z = zCopy.outputRef ∧
        (Frame.ofMountain ambient).cell packet.pair.z = zCopy.read.outputCell := by
    rcases packet.pair.z_origin with ⟨hUnchanged, _⟩ | ⟨_, zCopy, hRef, hCell⟩
    · exact (not_lt_of_ge hUnchanged hBlockerRight).elim
    · exact ⟨zCopy, hRef, hCell⟩
  have hZRef : Frame.ref comparison.pair.z = (zCopy.extend preserved).outputRef := by
    change Frame.ref (preserved.mapNode packet.pair.z) = zCopy.outputRef
    rw [preserved.mapNode_ref]
    exact hZRefLocal
  have copiedPath := (s.recorded_effective_path history hLast packet.source_path
    hBlockerRight hQBefore candidateCopy zCopy).preserve preserved
  have hSourceUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index := by
    intro hm
    obtain ⟨marker, hMarker, hi⟩ := List.mem_map.mp hm
    have hRef : marker = Frame.ref source := congrArg₂ Ref.mk (p.marker_iff.mp hMarker).1 hi
    exact p.fixed_parent_not_marked packet.source_parent hFixed (hRef ▸ hMarker)
  have hCandidateUnmarked := packet.candidate_unmarked_of_copied_fixed_blocker hFixed hBlockerRight
  have hDistinct : packet.candidate ≠ parent := by
    intro he
    have hLess : parent.1.val < packet.candidate.1.val := hFixed.trans hQRight
    exact (ne_of_lt hLess) (congrArg (fun node => node.1.val) he).symm
  obtain ⟨actual, candidate, hActualRef, hCandidateRef, hQ, _⟩ :=
    comparison.pair.uCopy.candidate_eq_nondirect_of_unmarked_pair hLast hValid hSourceUnmarked
      (candidateCopy.extend preserved) packet.source_parent packet.source_candidate hCandidateUnmarked hDistinct
  have hActual : actual = comparison.pair.u := Executable.ref_injective _
    (hActualRef.trans comparison.pair.u_ref.symm)
  subst actual
  have path := copiedPath.toParentPath_of_recognition hValid.toOrdered hLeft hCandidateRef hZRef
    (Frame.Q_real hValid.toOrdered comparison.pair.u_real hQ)
    (Frame.Q_column_lt hValid.toOrdered hQ)
  have hZP := hLeft comparison.pair.z comparison.pair.parent
    ((path.column_le hValid.toOrdered).trans_lt (Frame.Q_column_lt hValid.toOrdered hQ))
    comparison.pair.z_real comparison.pair.z_parent
  obtain ⟨actualParent, hActualParent, _, _, hSmall, _⟩ :=
    hSums.rawParent_upper hValid comparison.pair.u_real comparison.pair.u_upper
  have he : actualParent = comparison.pair.parent :=
    Option.some.inj (hActualParent.symm.trans comparison.pair.u_parent)
  subst actualParent
  have hBarrier := comparison.fixed_parent_barrier hLast hLegal hRun hFixed
  have hP := Frame.P_of_record_barrier hValid.toOrdered hQ path hZP hBarrier hSmall
  exact comparison.pair.u_parent.trans hP.symm

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem fixed_copied_blocker_recognition (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent : (Frame.ofMountain p.reduced).Node}
    (packet : AnySourceBlockerPacket p origin.block origin.start origin.references execution.source parent
      (origin.before.push origin.column))
    (hFixed : parent.1.val < p.root.column)
    (hBlockerRight : p.root.column < packet.blocker.1.val)
    (hRef : Frame.ref node = execution.copy.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node := by
  let comparison := packet.extend origin.preserved
  have hCurrent : comparison.pair.u = node := Executable.ref_injective _
    (comparison.pair.u_ref.trans ((comparison.pair.uCopy.unique execution.copy).1.trans hRef.symm))
  have hBefore : execution.source.1.val < origin.sourceColumn + 1 := by
    rw [execution.source_column]
    omega
  have hLeftAtU : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < comparison.pair.u.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father := by
    simpa only [hCurrent] using hLeft
  have hRecognized := origin.after_state.preserved_fixed_copied_blocker_recognition
    origin.after_history hLast packet hBefore origin.preserved
    (build_success_legal p.initial_build) hRun hFixed hBlockerRight hLeftAtU
  change (Frame.ofMountain result).rawParent comparison.pair.u =
    (Frame.ofMountain result).P comparison.pair.u at hRecognized
  simpa only [hCurrent] using hRecognized

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.preserved_fixed_copied_blocker_recognition
#print axioms OmegaY.Expansion.ExecutedNodeCopy.fixed_copied_blocker_recognition
