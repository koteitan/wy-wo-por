/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSpliceIndices.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualSpliceEdgeOrigins
import OmegaY.Expansion.InitialControlKeys

/-! Literal finite-index maps for the actual loop graphs. The initial
graph is the original complete prefix; the local splice and global source
transports agree after identifying their proven physical dimensions. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem PreservesColumns.eq_of_complete_size {before after : Mountain}
    (preserved : PreservesColumns before after) (hSize : before.size = after.size) :
    before = after := by
  apply Array.ext_getElem?
  intro column
  by_cases hBefore : column < before.size
  · exact (preserved column hBefore).symm
  · rw [Array.getElem?_eq_none (Nat.le_of_not_gt hBefore),
      Array.getElem?_eq_none (by omega : after.size ≤ column)]

namespace Preparation
variable {front : List Nat} {last : Nat} (p : Preparation front last)

theorem spliceMountain_zero (hLast : 1 < last) :
    p.spliceMountain hLast 0 = p.initial.pop := by
  have hSize : p.initial.pop.size = p.reduced.pop.size := by
    rw [p.initial_pop_size, Array.size_pop, p.reduced_size_eq]
    omega
  have hPreserved : PreservesColumns p.initial.pop p.reduced.pop :=
    p.initial_pop_preserved_reduced.pop_of_size (by
      rw [p.initial_pop_size, p.reduced_size_eq]
      omega)
  simpa only [spliceMountain, p.physicalBlock_zero] using
    (hPreserved.eq_of_complete_size hSize).symm

noncomputable def spliceCut (hLast : 1 < last) (block : Nat) :
    Fin (p.spliceMountain hLast block).size :=
  Fin.cast (p.spliceMountain_size hLast block).symm (Splice.blockCut p.root_before_last block)

@[simp] theorem spliceCut_val (hLast : 1 < last) (block : Nat) :
    (p.spliceCut hLast block).val = p.root.column + block * (front.length - p.root.column) := rfl

theorem spliceCut_width (hLast : 1 < last) (block : Nat) :
    Splice.width (p.spliceCut hLast block) = (p.spliceMountain hLast (block + 1)).size := by
  change (p.spliceMountain hLast block).size +
    ((p.spliceMountain hLast block).size - (p.spliceCut hLast block).val) = _
  rw [p.spliceCut_val, p.spliceMountain_size, p.spliceMountain_size]
  exact Splice.width_blockCut p.root_before_last block

noncomputable def spliceSource (hLast : 1 < last) (block : Nat) (column : Fin front.length) :
    Fin (p.spliceMountain hLast block).size :=
  Fin.cast (p.spliceMountain_size hLast block).symm (Splice.blockSource p.root_before_last block column)

noncomputable def spliceMoved (hLast : 1 < last) (block : Nat)
    (column : Fin (p.spliceMountain hLast block).size) :
    Fin (p.spliceMountain hLast (block + 1)).size :=
  Fin.cast (p.spliceCut_width hLast block) (Splice.moved (p.spliceCut hLast block) column)

theorem spliceSource_val (hLast : 1 < last) (block : Nat) (column : Fin front.length) :
    (p.spliceSource hLast block column).val =
      if column.val < p.root.column then column.val
      else column.val + block * (front.length - p.root.column) := by
  unfold spliceSource Splice.blockSource
  split <;> rfl

theorem spliceMoved_source (hLast : 1 < last) (block : Nat) (column : Fin front.length) :
    p.spliceMoved hLast block (p.spliceSource hLast block column) =
      p.spliceSource hLast (block + 1) column := by
  apply Fin.ext
  change (Splice.moved (p.spliceCut hLast block) (p.spliceSource hLast block column)).val =
    (Splice.blockSource p.root_before_last (block + 1) column).val
  have hTyped := congrArg Fin.val (Splice.blockMoved_source p.root_before_last block column)
  by_cases hi : (Splice.blockSource p.root_before_last block column).val <
      (Splice.blockCut p.root_before_last block).val
  · simpa only [spliceMoved, spliceSource, spliceCut, Fin.val_cast,
      Splice.blockMoved, Splice.moved, Splice.old, Fin.lt_def, hi, ↓reduceDIte,
      Fin.val_mk, p.spliceMountain_size] using hTyped
  · simpa only [spliceMoved, spliceSource, spliceCut, Fin.val_cast,
      Splice.blockMoved, Splice.moved, Splice.old, Fin.lt_def, hi, ↓reduceDIte,
      Fin.val_mk, p.spliceMountain_size] using hTyped

theorem spliceSource_root (hLast : 1 < last) (block : Nat) :
    p.spliceSource hLast block ⟨p.root.column, p.root_before_last⟩ = p.spliceCut hLast block := by
  apply Fin.ext
  simp only [spliceSource, spliceCut, Splice.blockSource_root]

theorem spliceCut_next_boundary (hLast : 1 < last) (block : Nat) :
    (p.spliceCut hLast (block + 1)).val = (p.spliceMountain hLast block).size := by
  rw [p.spliceCut_val, p.spliceMountain_size]
  exact Splice.blockCut_succ p.root_before_last block

theorem spliceMoved_cut_boundary (hLast : 1 < last) (block : Nat) :
    (p.spliceMoved hLast block (p.spliceCut hLast block)).val =
      (p.physicalBlock hLast block).size - 1 := by
  rw [← p.spliceSource_root hLast block, p.spliceMoved_source, p.spliceSource_root,
    p.spliceCut_next_boundary, p.spliceMountain_boundary_column]

theorem expandDiagram_eq_spliceMountain_all (hLast : 1 < last) (copies : Nat) :
    expandDiagram (front ++ [last]) copies = .ok (p.spliceMountain hLast copies) := by
  cases copies with
  | zero =>
      rw [p.spliceMountain_zero]
      simp [expandDiagram, p.initial_build, Except.mapError]
  | succ copies => exact p.expandDiagram_eq_spliceMountain hLast (by omega)

end Preparation
end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.spliceMountain_zero
#print axioms OmegaY.Expansion.Preparation.spliceCut_width
#print axioms OmegaY.Expansion.Preparation.spliceMoved_source
#print axioms OmegaY.Expansion.Preparation.spliceMoved_cut_boundary
#print axioms OmegaY.Expansion.Preparation.expandDiagram_eq_spliceMountain_all
