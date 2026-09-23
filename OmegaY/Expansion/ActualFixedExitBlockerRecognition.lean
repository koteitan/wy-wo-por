/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualFixedExitBlockerRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FixedCopiedBlockerCases
import OmegaY.Expansion.ActualHighFixedCandidateRecognition

/-!
# Recognition when the source record chain jumps past the root column

The copied prePath of the genuine source path ends in an actual fixed-parent
edge. Its remaining good-part path is preserved completely. Marker closure
excludes a marked candidate, so the actual new Q is its effective copy.
This closes the direct good-part exit without a boundary-path assumption.
-/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem Preparation.unmarked_before_fixed_exit
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {candidate lastBad exited : (Frame.ofMountain p.reduced).Node}
    (path : ParentPath (Frame.ofMountain p.reduced) candidate lastBad)
    (hExit : (Frame.ofMountain p.reduced).P lastBad = some exited)
    (hRight : p.root.column < lastBad.1.val) (hGood : exited.1.val < p.root.column) :
    candidate.2.val ∉ (p.marked[candidate.1.val]?.getD []).map Ref.index := by
  intro hm
  obtain ⟨marker, hMarker, hi⟩ := List.mem_map.mp hm
  have hRef : marker = Frame.ref candidate := congrArg₂ Ref.mk (p.marker_iff.mp hMarker).1 hi
  exact p.fixed_parent_not_marked hExit hGood
    (p.marked_at_parent_path_right path (hRef ▸ hMarker) hRight)

theorem DynamicBlockState.preserved_fixed_exit_blocker_recognition
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
    {lastBad exited : (Frame.ofMountain p.reduced).Node}
    (prePath : ParentPath (Frame.ofMountain p.reduced) packet.candidate lastBad)
    (hExit : (Frame.ofMountain p.reduced).P lastBad = some exited)
    (hRight : p.root.column < lastBad.1.val) (hGood : exited.1.val < p.root.column)
    (tail : ParentPath (Frame.ofMountain p.reduced) exited packet.blocker)
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
  have hQRight := hRight.trans_le (prePath.column_le hNormal.toOrdered)
  have hQBefore := (Frame.Q_column_lt hNormal.toOrdered packet.source_candidate).trans hBefore
  obtain ⟨candidateCopy⟩ := s.prior_effective_occurrence history hLast hQRight hQBefore
  have hSourceUnmarked : source.2.val ∉ (p.marked[source.1.val]?.getD []).map Ref.index := by
    intro hm
    obtain ⟨marker, hMarker, hi⟩ := List.mem_map.mp hm
    have hRef : marker = Frame.ref source := congrArg₂ Ref.mk (p.marker_iff.mp hMarker).1 hi
    exact p.fixed_parent_not_marked packet.source_parent hFixed (hRef ▸ hMarker)
  have hCandidateUnmarked := p.unmarked_before_fixed_exit prePath hExit hRight hGood
  have hDistinct : packet.candidate ≠ parent := by
    intro he
    exact (ne_of_lt (hFixed.trans hQRight)) (congrArg (fun node => node.1.val) he).symm
  obtain ⟨actual, candidate, hActualRef, hCandidateRef, hQ, _⟩ :=
    comparison.pair.uCopy.candidate_eq_nondirect_of_unmarked_pair hLast hValid hSourceUnmarked
      (candidateCopy.extend preserved) packet.source_parent packet.source_candidate hCandidateUnmarked hDistinct
  have hActual : actual = comparison.pair.u := Executable.ref_injective _
    (hActualRef.trans comparison.pair.u_ref.symm)
  subst actual
  have sourcePreserved := s.base_ambient.trans preserved
  have hCopiedPath := (s.recorded_effective_path_to_fixed history hLast prePath hExit
    hRight hQBefore hGood candidateCopy).1.preserve preserved
  have hFirstPath := hCopiedPath.toParentPath_of_recognition hValid.toOrdered hLeft hCandidateRef
    (sourcePreserved.mapNode_ref exited) (Frame.Q_real hValid.toOrdered comparison.pair.u_real hQ)
    (Frame.Q_column_lt hValid.toOrdered hQ)
  have hTail := sourcePreserved.mapNode_parentPath hNormal.toOrdered hValid.toOrdered tail
  have hBlockerGood := (tail.column_le hNormal.toOrdered).trans_lt hGood
  have hZRef : Frame.ref comparison.pair.z = Frame.ref packet.blocker := by
    rcases comparison.pair.z_origin with ⟨_, hRef, _⟩ | ⟨hMoved, _⟩
    · exact hRef
    · exact ((not_lt_of_ge hBlockerGood.le) hMoved).elim
  have hZNode : sourcePreserved.mapNode packet.blocker = comparison.pair.z :=
    Executable.ref_injective _ ((sourcePreserved.mapNode_ref packet.blocker).trans hZRef.symm)
  have path := hFirstPath.trans hTail
  rw [hZNode] at path
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

theorem fixed_exit_blocker_recognition (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent : (Frame.ofMountain p.reduced).Node}
    (packet : AnySourceBlockerPacket p origin.block origin.start origin.references execution.source parent
      (origin.before.push origin.column))
    (hFixed : parent.1.val < p.root.column)
    {lastBad exited : (Frame.ofMountain p.reduced).Node}
    (prePath : ParentPath (Frame.ofMountain p.reduced) packet.candidate lastBad)
    (hExit : (Frame.ofMountain p.reduced).P lastBad = some exited)
    (hRight : p.root.column < lastBad.1.val) (hGood : exited.1.val < p.root.column)
    (tail : ParentPath (Frame.ofMountain p.reduced) exited packet.blocker)
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
  have hRecognized := origin.after_state.preserved_fixed_exit_blocker_recognition
    origin.after_history hLast packet hBefore origin.preserved
    (build_success_legal p.initial_build) hRun hFixed prePath hExit hRight hGood tail hLeftAtU
  change (Frame.ofMountain result).rawParent comparison.pair.u =
    (Frame.ofMountain result).P comparison.pair.u at hRecognized
  simpa only [hCurrent] using hRecognized

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.unmarked_before_fixed_exit
#print axioms OmegaY.Expansion.DynamicBlockState.preserved_fixed_exit_blocker_recognition
#print axioms OmegaY.Expansion.ExecutedNodeCopy.fixed_exit_blocker_recognition

