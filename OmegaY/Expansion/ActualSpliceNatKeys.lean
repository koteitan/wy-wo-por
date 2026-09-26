/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSpliceNatKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSpliceFacts
import OmegaY.Expansion.ActualCopiedKeyBound

/-! Natural-column readings of the actual finite splice templates.
These are exact finite reindexings; infinity coordinates remain infinity. -/

namespace OmegaY.Keys

theorem template_le_of_nat_eval_le {m n : Nat} (left right : Template m n)
    (h : eval left (fun c => c.val) ≤ eval right (fun c => c.val)) :
    templateKey left ≤ templateKey right := by
  by_contra hn
  exact (not_lt_of_ge h) (eval_lt_of_template_lt right left (fun c => c.val)
    (fun _ _ hlt => hlt) (lt_of_not_ge hn))

end OmegaY.Keys

namespace OmegaY.Expansion.Preparation
open Canonical Geometry Frame
variable {front : List Nat} {last : Nat} (p : Preparation front last)

theorem spliceFact_moved_column (block : Nat) (column : Fin p.initial.pop.size) :
    (Splice.moved (Splice.blockCut p.root_before_last block)
      (Splice.blockSource p.root_before_last block (Fin.cast p.initial_pop_size column))).val =
      copiedKeyColumn p.root.column ((block + 1) * (p.reduced.size - 1 - p.root.column)) column.val := by
  have h := congrArg Fin.val (Splice.blockMoved_source p.root_before_last block
    (Fin.cast p.initial_pop_size column))
  change (Splice.moved (Splice.blockCut p.root_before_last block)
    (Splice.blockSource p.root_before_last block (Fin.cast p.initial_pop_size column))).val =
      (Splice.blockSource p.root_before_last (block + 1) (Fin.cast p.initial_pop_size column)).val at h
  refine h.trans ?_
  rw [p.reduced_block_width]
  by_cases hBefore : column.val < p.root.column
  · simp only [Splice.blockSource, copiedKeyColumn, Fin.val_cast, hBefore, ↓reduceDIte, ↓reduceIte]
  · simp only [Splice.blockSource, copiedKeyColumn, Fin.val_cast, hBefore, ↓reduceDIte, ↓reduceIte]

theorem spliceLocalEdgeAtom_nat_eval (hLast : 1 < last) (D block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1)))) :
    Keys.eval (p.spliceLocalEdgeAtom hLast D block edge).key (fun column => column.val) =
      Keys.eval (edge.keyTemplate (p.spliceMountain_valid hLast (block + 1)).toOrdered D)
        (fun column => column.val) := by
  change Keys.eval (Keys.relabel (Keys.relabel
    (edge.keyTemplate (p.spliceMountain_valid hLast (block + 1)).toOrdered D)
    (Fin.cast (p.spliceMountain_size hLast (block + 1))))
    (Fin.cast (Splice.width_blockCut p.root_before_last block).symm)) (fun column => column.val) = _
  simp only [Keys.eval_relabel]
  rfl

theorem movedSpliceFact_nat_eval (D block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain p.initial.pop)) :
    Keys.eval (Keys.relabel
        (Splice.mapAtom (Splice.blockSource p.root_before_last block)
          (Splice.blockSource_strictMono p.root_before_last block) (p.initialSpliceEdgeAtom D edge)).key
        (Splice.moved (Splice.blockCut p.root_before_last block))) (fun column => column.val) =
      Keys.eval (edge.keyTemplate p.initial_valid.pop.toOrdered D)
        (fun column => copiedKeyColumn p.root.column
          ((block + 1) * (p.reduced.size - 1 - p.root.column)) column.val) := by
  change Keys.eval (Keys.relabel (Keys.relabel (Keys.relabel
      (edge.keyTemplate p.initial_valid.pop.toOrdered D) (Fin.cast p.initial_pop_size))
      (Splice.blockSource p.root_before_last block))
      (Splice.moved (Splice.blockCut p.root_before_last block))) (fun column => column.val) = _
  simp only [Keys.eval_relabel]
  apply congrArg (Keys.eval (edge.keyTemplate p.initial_valid.pop.toOrdered D))
  funext column
  exact p.spliceFact_moved_column block column

end OmegaY.Expansion.Preparation

#print axioms OmegaY.Expansion.Preparation.spliceFact_moved_column
#print axioms OmegaY.Expansion.Preparation.spliceLocalEdgeAtom_nat_eval
#print axioms OmegaY.Expansion.Preparation.movedSpliceFact_nat_eval
