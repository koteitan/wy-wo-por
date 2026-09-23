/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualOrdinarySplice.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSpliceFacts
import OmegaY.Expansion.ActualSpliceNatKeys
import OmegaY.Expansion.ActualFillCopiedKey
import OmegaY.Expansion.ActualCopiedKeyLabels
import OmegaY.Expansion.SupportedDimension

/-! Ordinary newly added columns use literal moved internal reserves.
The source edge and complete key bound are recovered from actual copying,
including fills. Its block and its strict interior source column follow
from the physical target column, rather than being supplied as an oracle. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem ActualCopiedKeyBound.ordinary_coordinates
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {hLast : 1 < last} {D block : Nat}
    {edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1)))}
    (bound : ActualCopiedKeyBound p (p.spliceMountain hLast (block + 1))
      (p.spliceMountain_valid hLast (block + 1)).toOrdered edge D)
    (hNew : (p.spliceMountain hLast block).size < edge.lower.1.val) :
    bound.block = block + 1 ∧ bound.source.lower.1.val < front.length := by
  have hRight := bound.source_right
  have hSourceBound := bound.source_bound
  rw [p.reduced_size_eq] at hSourceBound
  have hChild := bound.child_column
  rw [copiedKeyColumn, if_neg (not_lt_of_ge hRight.le), p.reduced_block_width] at hChild
  have hTarget : edge.lower.1.val < (p.spliceMountain hLast (block + 1)).size := edge.lower.1.isLt
  simp only [p.spliceMountain_size, Splice.blockWidth, Nat.add_mul, Nat.one_mul] at hNew hTarget
  have hRoot := p.root_before_last
  have hLower : block + 1 ≤ bound.block := by
    by_contra hn
    have hk : bound.block ≤ block := by omega
    have hMul := Nat.mul_le_mul_right (front.length - p.root.column) hk
    omega
  have hUpper : bound.block ≤ block + 1 := by
    by_contra hn
    have hk : block + 2 ≤ bound.block := by omega
    have hMul := Nat.mul_le_mul_right (front.length - p.root.column) hk
    simp only [Nat.add_mul] at hMul
    omega
  have he : bound.block = block + 1 := by omega
  refine ⟨he, ?_⟩
  rw [he, Nat.add_mul, Nat.one_mul] at hChild
  omega

namespace Preparation
variable {front : List Nat} {last : Nat} (p : Preparation front last)

/-- Every actual ordinary new edge is supplied by a literal moved member
of the complete original internal reserve. The inequality also includes
actual fill edges, and does not assume an output edge classification. -/
theorem ordinary_splice_classified (hLast : 1 < last) (D block : Nat)
    (hDimension : MountainKeyDimension p.initial D)
    (N : List (Model.TopAtom (D + 1) (Splice.blockWidth front.length p.root.column block)))
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1))))
    (hNew : (p.spliceMountain hLast block).size < edge.lower.1.val) :
    Splice.ReservoirClassified (Splice.blockCut p.root_before_last block)
      (p.spliceGraph hLast D block) (p.spliceFacts D block) N
      (p.spliceLocalEdgeAtom hLast D block edge) := by
  have hRun := p.expandDiagram_eq_spliceMountain hLast (show 0 < block + 1 by omega)
  have hCopied : p.reduced.size ≤ edge.lower.1.val := by
    have hn := p.spliceMountain_size hLast block
    rw [p.reduced_size_eq]
    unfold Splice.blockWidth at hn
    omega
  obtain ⟨bound⟩ := p.copied_edge_key_bound hLast (by omega) hRun edge hCopied D
    (p.spliceMountain_key_dimension hLast hDimension (block + 1))
  have hCoordinates := bound.ordinary_coordinates hNew
  have hBlock := hCoordinates.1
  let preserved := p.initial_pop_preserved_reduced
  obtain ⟨oldEdge, hSource⟩ := preserved.storedEdge_preimage p.reduced_valid.toOrdered bound.source
    (hCoordinates.2.trans_eq p.initial_pop_size.symm)
  let oldAtom := p.initialSpliceEdgeAtom D oldEdge
  let fact := Splice.mapAtom (Splice.blockSource p.root_before_last block)
    (Splice.blockSource_strictMono p.root_before_last block) oldAtom
  have hFact : fact ∈ p.spliceFacts D block :=
    List.mem_map.mpr ⟨oldAtom, p.initialSpliceEdgeAtom_mem D oldEdge, rfl⟩
  have hOldParent : oldEdge.parent.1.val = bound.source.parent.1.val :=
    (preserved.mapNode_column oldEdge.parent).symm.trans
      (congrArg (fun actual => actual.parent.1.val) hSource)
  have hOldChild : oldEdge.lower.1.val = bound.source.lower.1.val :=
    (preserved.mapNode_column oldEdge.lower).symm.trans
      (congrArg (fun actual => actual.lower.1.val) hSource)
  have hParent : (p.spliceLocalEdgeAtom hLast D block edge).parent =
      Splice.moved (Splice.blockCut p.root_before_last block) fact.parent := by
    apply Fin.ext
    change edge.parent.1.val = _
    calc
      edge.parent.1.val = copiedKeyColumn p.root.column
          ((block + 1) * (p.reduced.size - 1 - p.root.column)) bound.source.parent.1.val := by
        simpa only [hBlock] using bound.parent_column
      _ = copiedKeyColumn p.root.column
          ((block + 1) * (p.reduced.size - 1 - p.root.column)) oldEdge.parent.1.val :=
        congrArg _ hOldParent.symm
      _ = _ := (p.spliceFact_moved_column block oldEdge.parent.1).symm
  have hChild : (p.spliceLocalEdgeAtom hLast D block edge).child =
      Splice.moved (Splice.blockCut p.root_before_last block) fact.child := by
    apply Fin.ext
    change edge.lower.1.val = _
    calc
      edge.lower.1.val = copiedKeyColumn p.root.column
          ((block + 1) * (p.reduced.size - 1 - p.root.column)) bound.source.lower.1.val := by
        simpa only [hBlock] using bound.child_column
      _ = copiedKeyColumn p.root.column
          ((block + 1) * (p.reduced.size - 1 - p.root.column)) oldEdge.lower.1.val :=
        congrArg _ hOldChild.symm
      _ = _ := (p.spliceFact_moved_column block oldEdge.lower.1).symm
  let sourceLabels : Fin p.reduced.size → Nat := fun column => copiedKeyColumn p.root.column
    ((block + 1) * (p.reduced.size - 1 - p.root.column)) column.val
  have hReducedKey : Keys.eval (bound.source.keyTemplate p.reduced_valid.toOrdered D) sourceLabels =
      Keys.eval (oldEdge.keyTemplate p.initial_valid.pop.toOrdered D)
        (sourceLabels ∘ preserved.keyColumn) :=
    (congrArg (fun source => Keys.eval (source.keyTemplate p.reduced_valid.toOrdered D) sourceLabels)
      hSource).symm.trans
      (preserved.storedEdge_key_eval p.initial_valid.pop.toOrdered p.reduced_valid.toOrdered oldEdge D sourceLabels)
  have hMovedKey : Keys.eval (Keys.relabel fact.key (Splice.moved (Splice.blockCut p.root_before_last block)))
      (fun column => column.val) =
      Keys.eval (bound.source.keyTemplate p.reduced_valid.toOrdered D) sourceLabels := by
    change Keys.eval (Keys.relabel (Keys.relabel (Keys.relabel
        (oldEdge.keyTemplate p.initial_valid.pop.toOrdered D) (Fin.cast p.initial_pop_size))
        (Splice.blockSource p.root_before_last block))
        (Splice.moved (Splice.blockCut p.root_before_last block))) (fun column => column.val) = _
    simp only [Keys.eval_relabel]
    apply Eq.trans _ hReducedKey.symm
    apply congrArg (Keys.eval (oldEdge.keyTemplate p.initial_valid.pop.toOrdered D))
    funext column
    exact p.spliceFact_moved_column block column
  have hActualKey : Keys.eval (p.spliceLocalEdgeAtom hLast D block edge).key
      (fun column => column.val) =
      Keys.eval (edge.keyTemplate (p.spliceMountain_valid hLast (block + 1)).toOrdered D)
        (fun column => column.val) := by
    change Keys.eval (Keys.relabel (Keys.relabel
      (edge.keyTemplate (p.spliceMountain_valid hLast (block + 1)).toOrdered D)
      (Fin.cast (p.spliceMountain_size hLast (block + 1))))
      (Fin.cast (Splice.width_blockCut p.root_before_last block).symm)) (fun column => column.val) = _
    simp only [Keys.eval_relabel]
    rfl
  have hNat : Keys.eval (p.spliceLocalEdgeAtom hLast D block edge).key (fun column => column.val) ≤
      Keys.eval (Keys.relabel fact.key (Splice.moved (Splice.blockCut p.root_before_last block)))
        (fun column => column.val) := by
    rw [hActualKey, hMovedKey]
    have hKey := bound.key_le
    rw [hBlock] at hKey
    exact hKey
  exact Or.inr (Or.inl ⟨fact, hFact, hParent, hChild, Keys.template_le_of_nat_eval_le _ _ hNat⟩)

end Preparation
end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualCopiedKeyBound.ordinary_coordinates
#print axioms OmegaY.Expansion.Preparation.ordinary_splice_classified
