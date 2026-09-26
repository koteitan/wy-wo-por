/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualBoundarySplice.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BoundaryKeyClassification
import OmegaY.Expansion.ActualSpliceNatKeys

/-! Boundary edges satisfy the exact finite classification consumed by
reflection. All lower reserves are kept; grafted edges use the ordinary
internal reserve. No edge relation or successor representation is assumed. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

namespace RootGeometry
variable {front : List Nat} {last : Nat} {p : Preparation front last}

theorem virtualSpliceFact_parent_column (g : RootGeometry p) (D block : Nat)
    (edge : g.LowerEdge) :
    (Splice.mapTop (Splice.blockSource p.root_before_last block)
      (g.initialSpliceVirtualAtom D edge)).parent.val =
      copiedKeyColumn p.root.column (block * (front.length - p.root.column)) edge.val.parent.1.val := by
  change (Splice.blockSource p.root_before_last block
    (Fin.cast p.initial_pop_size (g.lowerAtom D edge).parent)).val = _
  have hValue : (g.lowerAtom D edge).parent.val = edge.val.parent.1.val := rfl
  by_cases hGood : edge.val.parent.1.val < p.root.column
  · simp only [Splice.blockSource, copiedKeyColumn, Fin.val_cast, hValue, hGood, ↓reduceDIte, ↓reduceIte]
  · simp only [Splice.blockSource, copiedKeyColumn, Fin.val_cast, hValue, hGood, ↓reduceDIte, ↓reduceIte]

theorem oldVirtualSpliceFact_nat_eval (g : RootGeometry p) (D block : Nat)
    (edge : g.LowerEdge) :
    Keys.eval (Keys.relabel
        (Splice.mapTop (Splice.blockSource p.root_before_last block)
          (g.initialSpliceVirtualAtom D edge)).key
        (Splice.old (Splice.blockCut p.root_before_last block))) (fun c => c.val) =
      Keys.eval (edge.val.keyTemplate p.initial_valid.toOrdered D)
        (fun c => copiedKeyColumn p.root.column (block * (front.length - p.root.column)) c.val) := by
  have hTop := edge.val.topAtom_key_eval p.initial_valid.toOrdered D p.initial.pop.size
    (edge.property.1.trans p.initial_pop_size.symm)
    (PreservesColumns.pop_prefix p.initial).size_le
    (fun c => copiedKeyColumn p.root.column (block * (front.length - p.root.column)) c.val)
  change Keys.eval (g.lowerAtom D edge).key
      (fun c => copiedKeyColumn p.root.column (block * (front.length - p.root.column)) c.val) = _ at hTop
  apply Eq.trans _ hTop
  change Keys.eval (Keys.relabel (Keys.relabel (Keys.relabel
      (g.lowerAtom D edge).key (Fin.cast p.initial_pop_size))
      (Splice.blockSource p.root_before_last block))
      (Splice.old (Splice.blockCut p.root_before_last block))) (fun c => c.val) = _
  simp only [Keys.eval_relabel]
  refine (Keys.eval_relabel (g.lowerAtom D edge).key (Fin.cast p.initial_pop_size)
    (((fun c => c.val) ∘ Splice.old (Splice.blockCut p.root_before_last block)) ∘
      Splice.blockSource p.root_before_last block)).trans ?_
  apply congrArg (Keys.eval (g.lowerAtom D edge).key)
  funext column
  change (Splice.blockSource p.root_before_last block (Fin.cast p.initial_pop_size column)).val = _
  by_cases hGood : column.val < p.root.column
  · simp only [Splice.blockSource, copiedKeyColumn, Fin.val_cast, hGood, ↓reduceDIte, ↓reduceIte]
  · simp only [Splice.blockSource, copiedKeyColumn, Fin.val_cast, hGood, ↓reduceDIte, ↓reduceIte]

end RootGeometry

namespace Preparation
variable {front : List Nat} {last : Nat} (p : Preparation front last)

theorem boundary_splice_classified (g : RootGeometry p) (hLast : 1 < last) (D block : Nat)
    (hDimension : MountainKeyDimension p.initial D)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1))))
    (hColumn : edge.lower.1.val = (p.spliceMountain hLast block).size) :
    Splice.ReservoirClassified (Splice.blockCut p.root_before_last block)
      (p.spliceGraph hLast D block) (p.spliceFacts D block) (g.spliceVirtualFacts D block)
      (p.spliceLocalEdgeAtom hLast D block edge) := by
  cases p.boundary_original_key_origin g hLast block edge hColumn D hDimension with
  | lower old hParent hKey =>
    let demand := Splice.mapTop (Splice.blockSource p.root_before_last block)
      (g.initialSpliceVirtualAtom D old)
    have hMember : demand ∈ g.spliceVirtualFacts D block :=
      List.mem_map.mpr ⟨g.initialSpliceVirtualAtom D old, g.initialSpliceVirtualAtom_mem D old, rfl⟩
    have hp : (p.spliceLocalEdgeAtom hLast D block edge).parent =
        Splice.old (Splice.blockCut p.root_before_last block) demand.parent := by
      apply Fin.ext
      change edge.parent.1.val = demand.parent.val
      exact hParent.trans (g.virtualSpliceFact_parent_column D block old).symm
    have hc : (p.spliceLocalEdgeAtom hLast D block edge).child =
        Splice.boundary (Splice.blockCut p.root_before_last block) := by
      apply Fin.ext
      exact hColumn.trans (p.spliceMountain_size hLast block)
    have hk : Keys.templateKey (p.spliceLocalEdgeAtom hLast D block edge).key ≤
        Keys.templateKey (Keys.relabel demand.key (Splice.old (Splice.blockCut p.root_before_last block))) := by
      apply Keys.template_le_of_nat_eval_le
      rw [p.spliceLocalEdgeAtom_nat_eval, g.oldVirtualSpliceFact_nat_eval]
      exact hKey
    exact Or.inr (Or.inr ⟨demand, hMember, hp, hc, hk⟩)
  | grafted old hOldColumn hParent hKey =>
    let fact := Splice.mapAtom (Splice.blockSource p.root_before_last block)
      (Splice.blockSource_strictMono p.root_before_last block) (p.initialSpliceEdgeAtom D old)
    have hMember : fact ∈ p.spliceFacts D block :=
      List.mem_map.mpr ⟨p.initialSpliceEdgeAtom D old, p.initialSpliceEdgeAtom_mem D old, rfl⟩
    have hParentGood : old.parent.1.val < p.root.column :=
      (rawParent_column_lt p.initial_valid.pop.toOrdered old.parent_eq).trans_eq hOldColumn
    have hp : (p.spliceLocalEdgeAtom hLast D block edge).parent =
        Splice.moved (Splice.blockCut p.root_before_last block) fact.parent := by
      apply Fin.ext
      change edge.parent.1.val = (Splice.moved (Splice.blockCut p.root_before_last block)
        (Splice.blockSource p.root_before_last block (Fin.cast p.initial_pop_size old.parent.1))).val
      have hm := p.spliceFact_moved_column block old.parent.1
      have hFixed : copiedKeyColumn p.root.column
          ((block + 1) * (p.reduced.size - 1 - p.root.column)) old.parent.1.val = old.parent.1.val :=
        if_pos hParentGood
      exact hParent.trans (hm.trans hFixed).symm
    have hc : (p.spliceLocalEdgeAtom hLast D block edge).child =
        Splice.moved (Splice.blockCut p.root_before_last block) fact.child := by
      apply Fin.ext
      change edge.lower.1.val = (Splice.moved (Splice.blockCut p.root_before_last block)
        (Splice.blockSource p.root_before_last block (Fin.cast p.initial_pop_size old.lower.1))).val
      have hm := p.spliceFact_moved_column block old.lower.1
      apply Eq.trans _ hm.symm
      rw [hOldColumn, copiedKeyColumn, if_neg (lt_irrefl p.root.column),
        p.reduced_block_width, hColumn, p.spliceMountain_size]
      unfold Splice.blockWidth
      have hRoot := p.root_before_last
      simp only [Nat.add_mul, Nat.one_mul]
      omega
    have hk : Keys.templateKey (p.spliceLocalEdgeAtom hLast D block edge).key ≤
        Keys.templateKey (Keys.relabel fact.key (Splice.moved (Splice.blockCut p.root_before_last block))) := by
      apply Keys.template_le_of_nat_eval_le
      rw [p.spliceLocalEdgeAtom_nat_eval, p.movedSpliceFact_nat_eval, p.reduced_block_width]
      exact hKey
    exact Or.inr (Or.inl ⟨fact, hMember, hp, hc, hk⟩)

end Preparation
end OmegaY.Expansion

#print axioms OmegaY.Expansion.RootGeometry.oldVirtualSpliceFact_nat_eval
#print axioms OmegaY.Expansion.Preparation.boundary_splice_classified
