/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FixedCrossingRootCases.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFixedExitBlockerRecognition
import OmegaY.Expansion.ActualRootCandidateRange

/-!
# Every unresolved copied-candidate search actually visits the root column

The source chain either stays in copied columns, jumps directly into the
good part, or visits an actual root-column node. The first two alternatives
are numerically recognized. In the last alternative both source path pieces
are retained, and the actual current copy stays in that root node's original
row interval. No target boundary path or target candidate identity is assumed.
-/

namespace OmegaY.Geometry.Frame

theorem ParentPath.frontierAt_of_source_frontier {F : Frame} (hF : F.Normal)
    {source target : F.Node} (path : ParentPath F source target)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hFront : frontierAt hF.toOrdered cut hCut source.1 = source) :
    frontierAt hF.toOrdered cut hCut target.1 = target := by
  induction path with
  | refl _ => exact hFront
  | @cons source middle target hEdge tail ih =>
    have hMiddle := hF.frontierAt_parent hCut source.1 (by simpa only [hFront] using hEdge)
    exact ih hMiddle

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion
open Canonical Geometry Frame

namespace ExecutedNodeCopy

variable {front : List Nat} {last : Nat} {p : Preparation front last} {result : Mountain}
  {node : (Frame.ofMountain result).Node} {origin : CopiedNodeOrigin p result node}
  (execution : ExecutedNodeCopy origin)

theorem fixed_copied_candidate_root_cases (hLast : 1 < last) {copies : Nat}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    {parent candidate : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P execution.source = some parent)
    (hNondirect : (Frame.ofMountain p.reduced).Q execution.source ≠ some parent)
    (hFixed : parent.1.val < p.root.column)
    (hCandidate : (Frame.ofMountain p.reduced).Q execution.source = some candidate)
    (hCandidateRight : p.root.column < candidate.1.val)
    (hRef : Frame.ref node = execution.copy.outputRef)
    (hLeft : ∀ (current father : (Frame.ofMountain result).Node),
      current.1.val < node.1.val → Real current →
      (Frame.ofMountain result).rawParent current = some father →
        (Frame.ofMountain result).P current = some father) :
    (Frame.ofMountain result).rawParent node = (Frame.ofMountain result).P node ∨
      ∃ packet : AnySourceBlockerPacket p origin.block origin.start origin.references execution.source parent
          (origin.before.push origin.column),
        ∃ root : (Frame.ofMountain p.reduced).Node,
          root.1.val = p.root.column ∧ Real root ∧ packet.blocker.1.val ≤ p.root.column ∧
          ParentPath (Frame.ofMountain p.reduced) packet.candidate root ∧
          ParentPath (Frame.ofMountain p.reduced) root packet.blocker ∧
          (Frame.ofMountain p.reduced).height root ≤ execution.copy.read.outputCell.row ∧
          ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
            execution.copy.read.outputCell.row < (Frame.ofMountain p.reduced).height upper := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  rcases execution.fixed_nondirect_blocker_cases hLast hRun hParent hNondirect hFixed hRef hLeft with
    hRecognized | ⟨packet, hBlockerLeft⟩
  · exact Or.inl hRecognized
  · have hCandidateEq : packet.candidate = candidate :=
      Option.some.inj (packet.source_candidate.symm.trans hCandidate)
    have hPacketRight : p.root.column < packet.candidate.1.val := hCandidateEq ▸ hCandidateRight
    obtain ⟨lastBad, exited, prePath, hExit, tail, hRight, hNotRight⟩ :=
      packet.source_path.first_exit (inside := fun source => p.root.column < source.1.val)
        hPacketRight (not_lt_of_ge hBlockerLeft)
    by_cases hGood : exited.1.val < p.root.column
    · exact Or.inl (execution.fixed_exit_blocker_recognition
        hLast hRun packet hFixed prePath hExit hRight hGood tail hRef hLeft)
    · have hRootColumn : exited.1.val = p.root.column := by omega
      have rootPath : ParentPath F packet.candidate exited := prePath.trans (.cons hExit (.refl _))
      have hRealSource := Frame.real_of_value_pos hNormal.toOrdered
        ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
      have hCut := Frame.one_le_height hNormal.toOrdered hRealSource
      have hCandidateFront : frontierAt hNormal.toOrdered (F.height execution.source) hCut packet.candidate.1 =
          packet.candidate := by
        apply frontierAt_eq_of_upper_barrier hNormal.toOrdered hCut
          (Frame.Q_height_le hNormal.toOrdered packet.source_candidate)
        intro upper hUpper
        exact Frame.Q_upper_gt hNormal.toOrdered packet.source_candidate hUpper
      have hRootFront := rootPath.frontierAt_of_source_frontier hNormal hCut hCandidateFront
      have hRootSpec := frontierAt_spec hNormal.toOrdered hCut exited.1
      have hRootReal : Real exited := hRootFront ▸ hRootSpec.2.1
      have hRootLow : F.height exited ≤ F.height execution.source := by
        simpa only [hRootFront] using hRootSpec.2.2.1
      have hRootHigh : ∀ upper, F.upper exited = some upper → F.height execution.source < F.height upper := by
        simpa only [hRootFront] using hRootSpec.2.2.2.2
      refine Or.inr ⟨packet, exited, hRootColumn, hRootReal, hBlockerLeft, rootPath, tail,
        hRootLow.trans execution.copy.read.source_row_le_output, ?_⟩
      intro upper hUpper
      exact execution.copy.row_lt_root_height hLast
        ((congrArg Fin.val (Frame.upper_spec hUpper).1).trans hRootColumn)
        (hRootHigh upper hUpper)

end ExecutedNodeCopy
end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.ParentPath.frontierAt_of_source_frontier
#print axioms OmegaY.Expansion.ExecutedNodeCopy.fixed_copied_candidate_root_cases
