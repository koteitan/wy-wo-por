/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RootBoundaryTailRecognition.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighestRootCandidateRecognition
import OmegaY.Expansion.FixedCrossingRootCases

/-!
# Numerical completion after an actual path reaches the block boundary

This module closes the boundary-to-good-part tail of a genuine source
last-blocker packet. At lower root rows the projected path reaches the
old root. At the highest root it instead supplies a new last record and
its value barrier. The caller must still derive the actual new Q-to-boundary
path; no such path is inferred merely from source reachability.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace AnySourceBlockerPacket

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {source parent : (Frame.ofMountain p.reduced).Node}
  (packet : AnySourceBlockerPacket p block start references source parent result)

theorem recognize_of_root_boundary_path
    (hLast : 1 < last) {copies startCopies : Nat} (hCopies : 0 < copies)
    (hRun : expandDiagram (front ++ [last]) copies = .ok result)
    (hStartRun : (forIn (List.range startCopies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (preserved : PreservesColumns start result)
    (hStartValid : MountainValid start) (hWidth : 0 < start.size)
    {root : (Frame.ofMountain p.reduced).Node}
    (hRootReal : Real root) (hRootColumn : root.1.val = p.root.column)
    (tail : ParentPath (Frame.ofMountain p.reduced) root packet.blocker)
    (hRootLow : (Frame.ofMountain p.reduced).height root ≤ (Frame.ofMountain result).height packet.pair.u)
    (hRootHigh : ∀ upper, (Frame.ofMountain p.reduced).upper root = some upper →
      (Frame.ofMountain result).height packet.pair.u < (Frame.ofMountain p.reduced).height upper)
    (hLow : (Frame.ofMountain result).height packet.pair.u < p.lastTop.row)
    (hKnown : ∀ (node father : (Frame.ofMountain result).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain result).rawParent node = some father →
        (Frame.ofMountain result).P node = some father)
    {q : (Frame.ofMountain result).Node}
    (hQ : (Frame.ofMountain result).Q packet.pair.u = some q)
    {boundary : (Frame.ofMountain start).Node}
    (hBoundaryColumn : boundary.1.val = start.size - 1)
    (hBoundaryFront : frontierAt hStartValid.toOrdered
      ((Frame.ofMountain result).height packet.pair.u)
      (Frame.one_le_height (expandDiagram_valid_of_success (build_success_legal p.initial_build) hRun).toOrdered
        packet.pair.u_real) boundary.1 = boundary)
    (path : ParentPath (Frame.ofMountain result) q (preserved.mapNode boundary)) :
    (Frame.ofMountain result).P packet.pair.u = some packet.pair.parent := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hLegal := build_success_legal p.initial_build
  have hNormal := build_normal_of_success p.reduced_build
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hSourcePreserved := p.expandDiagram_reduced_preserved hLast hCopies hRun
  have hStartNormal := p.blocks_normal_of_left_recognition hLast hStartRun preserved hValid.toOrdered hKnown
  have hCut := Frame.one_le_height hValid.toOrdered packet.pair.u_real
  have hZLe : packet.blocker.1.val ≤ p.root.column :=
    (tail.column_le hNormal.toOrdered).trans_eq hRootColumn
  have hParentFixed : parent.1.val < p.root.column :=
    (Frame.P_column_lt hNormal.toOrdered packet.source_last_parent).trans_le hZLe
  have hParentRef : Frame.ref packet.pair.parent = Frame.ref parent := by
    rcases packet.pair.parent_origin with ⟨_, hRef, _⟩ | ⟨hRoot, _⟩ | ⟨hRight, _⟩
    · exact hRef
    · exact False.elim (ne_of_lt hParentFixed hRoot)
    · exact False.elim (not_lt_of_ge hParentFixed.le hRight)
  have heParent : hSourcePreserved.mapNode parent = packet.pair.parent :=
    Executable.ref_injective G ((hSourcePreserved.mapNode_ref parent).trans hParentRef.symm)
  have hZRef : Frame.ref packet.pair.z = Frame.ref packet.blocker := by
    rcases packet.pair.z_origin with ⟨_, hRef, _⟩ | ⟨hRight, _⟩
    · exact hRef
    · exact False.elim (not_lt_of_ge hZLe hRight)
  have heZ : hSourcePreserved.mapNode packet.blocker = packet.pair.z :=
    Executable.ref_injective G ((hSourcePreserved.mapNode_ref packet.blocker).trans hZRef.symm)
  have hSmall := ((expandDiagram_equations hLegal hRun).1.rawParent_value_lt
    hValid packet.pair.u_real packet.pair.u_parent).2
  have hBoundaryEq : frontierAt hStartValid.toOrdered (G.height packet.pair.u) hCut
      ⟨start.size - 1, by change start.size - 1 < start.size; omega⟩ = boundary := by
    have hc : (⟨start.size - 1, by change start.size - 1 < start.size; omega⟩ :
        Fin (Frame.ofMountain start).width) = boundary.1 := Fin.ext hBoundaryColumn.symm
    simpa only [hc] using hBoundaryFront
  by_cases hBefore : root.2.val < p.root.index
  · obtain ⟨upper, hUpper⟩ := p.root_upper_of_before_badRoot hRootColumn hBefore
    obtain ⟨original, hOriginalRef, _, hRootPath⟩ :=
      p.blocks_low_root_frontier_path_of_left_recognition hLast hStartRun preserved hValid.toOrdered
        hKnown hRootReal hRootColumn hBefore hUpper hStartValid hWidth hCut hRootLow (hRootHigh upper hUpper)
    rw [hBoundaryEq] at hRootPath
    have hMapped := preserved.mapNode_parentPath hStartNormal.toOrdered hValid.toOrdered hRootPath
    have heOriginal : preserved.mapNode original = hSourcePreserved.mapNode root :=
      Executable.ref_injective G ((preserved.mapNode_ref original).trans
        (hOriginalRef.trans (hSourcePreserved.mapNode_ref root).symm))
    rw [heOriginal] at hMapped
    have hTailMapped := hSourcePreserved.mapNode_parentPath hNormal.toOrdered hValid.toOrdered tail
    rw [heZ] at hTailMapped
    have hLastP := hSourcePreserved.mapNode_P hNormal.toOrdered hValid.toOrdered packet.source_last_parent
    rw [heZ, heParent] at hLastP
    exact Frame.P_of_record_barrier hValid.toOrdered hQ ((path.trans hMapped).trans hTailMapped)
      hLastP (packet.fixed_parent_barrier hLast hLegal hRun hParentFixed) hSmall
  · have hAt : root.2.val = p.root.index := by
      by_contra hn
      have hHigh := p.root_node_after_badRoot_is_high hLast hRootColumn (by omega)
      exact not_lt_of_ge (hHigh.trans hRootLow) hLow
    have hRootRef : Frame.ref root = p.root := congrArg₂ Ref.mk hRootColumn hAt
    have hSourceLarge : 1 < F.value source := by
      have hp := P_value hNormal.toOrdered packet.source_parent
      dsimp [F]
      omega
    have hRootLarge : 1 < F.value root :=
      (hSourceLarge.trans_le packet.source_value).trans_le (tail.value_le hNormal.toOrdered)
    obtain ⟨rootParent, hRootParent⟩ := hNormal.parent_exists hRootLarge
    obtain ⟨original, z, hOriginalRef, _, hRootPath, hLastEdge, hBarrier⟩ :=
      p.blocks_highest_root_records_at_cut hLast hStartRun preserved hValid.toOrdered hKnown
        hRootRef hRootParent hStartValid hWidth hCut hRootLow hLow
    rw [hBoundaryEq] at hRootPath
    have hMapped := preserved.mapNode_parentPath hStartNormal.toOrdered hValid.toOrdered hRootPath
    have hLastMapped := preserved.mapNode_P hStartNormal.toOrdered hValid.toOrdered hLastEdge
    have heOriginal : preserved.mapNode original = hSourcePreserved.mapNode rootParent :=
      Executable.ref_injective G ((preserved.mapNode_ref original).trans
        (hOriginalRef.trans (hSourcePreserved.mapNode_ref rootParent).symm))
    rw [heOriginal] at hLastMapped
    by_cases hSame : root = packet.blocker
    · have hRootP : F.P root = some parent := hSame ▸ packet.source_last_parent
      have heRootParent : rootParent = parent := Option.some.inj (hRootParent.symm.trans hRootP)
      rw [heRootParent, heParent] at hLastMapped
      have hValue : G.value packet.pair.u = F.value source :=
        (congrArg Cell.value packet.pair.u_cell).trans
          (packet.pair.uCopy.value_of_fixed_parent_expansion hLast hLegal hRun packet.source_parent hParentFixed)
      have hUBarrier : G.value packet.pair.u ≤ G.value (preserved.mapNode z) := by
        rw [hValue, show G.value (preserved.mapNode z) = (Frame.ofMountain start).value z from
          congrArg Cell.value (preserved.mapNode_cell z)]
        exact packet.source_value.trans (hSame ▸ hBarrier)
      exact Frame.P_of_record_barrier hValid.toOrdered hQ (path.trans hMapped) hLastMapped hUBarrier hSmall
    · have hTail : ParentPath F rootParent packet.blocker := by
        cases tail with
        | refl _ => exact (hSame rfl).elim
        | cons hEdge rest =>
          have he := Option.some.inj (hEdge.symm.trans hRootParent)
          exact he ▸ rest
      have hTailMapped := hSourcePreserved.mapNode_parentPath hNormal.toOrdered hValid.toOrdered hTail
      rw [heZ] at hTailMapped
      have hLastP := hSourcePreserved.mapNode_P hNormal.toOrdered hValid.toOrdered packet.source_last_parent
      rw [heZ, heParent] at hLastP
      exact Frame.P_of_record_barrier hValid.toOrdered hQ
        ((path.trans hMapped).trans (.cons hLastMapped hTailMapped)) hLastP
        (packet.fixed_parent_barrier hLast hLegal hRun hParentFixed) hSmall

end AnySourceBlockerPacket
end OmegaY.Expansion

#print axioms OmegaY.Expansion.AnySourceBlockerPacket.recognize_of_root_boundary_path
