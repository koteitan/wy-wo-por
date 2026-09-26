/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BoundaryKeySources.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualFillCopiedKey
import OmegaY.Expansion.ActualCopiedKeyLabels
import OmegaY.Expansion.ActualSpliceIndices
import OmegaY.Expansion.SupportedDimension

/-! A boundary retained between two physical blocks always comes from
the reduced source's last column. This includes the first boundary,
which is retained directly, and every later ordinary or filled copy. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

theorem ActualCopiedKeyBound.boundary_coordinates
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {result : Mountain} {hOrdered : (Frame.ofMountain result).Ordered}
    {edge : RealStoredEdge (Frame.ofMountain result)} {D : Nat}
    (bound : ActualCopiedKeyBound p result hOrdered edge D) {block : Nat}
    (hColumn : edge.lower.1.val = front.length + block * (front.length - p.root.column)) :
    bound.block = block ∧ bound.source.lower.1.val = front.length := by
  let width := front.length - p.root.column
  have hWidth : 0 < width := Nat.sub_pos_of_lt p.root_before_last
  have hOffset : width - 1 < width := by omega
  have hDistance : edge.lower.1.val - (p.root.column + 1) = width - 1 + block * width := by
    dsimp [width]
    omega
  have hBlock := bound.column_coordinates.1
  rw [p.reduced_block_width, hDistance,
    Nat.add_mul_div_right _ _ hWidth, Nat.div_eq_of_lt hOffset, Nat.zero_add] at hBlock
  have hChild := bound.child_column
  rw [copiedKeyColumn, if_neg (not_lt_of_ge bound.source_right.le),
    p.reduced_block_width, ← hBlock] at hChild
  exact ⟨hBlock.symm, by omega⟩

structure BoundaryKeyBound {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1))))
    (D : Nat) where
  source : RealStoredEdge (Frame.ofMountain p.reduced)
  source_last : source.lower.1.val = front.length
  parent_column : edge.parent.1.val = copiedKeyColumn p.root.column
    (block * (front.length - p.root.column)) source.parent.1.val
  key_le : Keys.eval (edge.keyTemplate (p.spliceMountain_valid hLast (block + 1)).toOrdered D)
      (fun c => c.val) ≤
    Keys.eval (source.keyTemplate p.reduced_valid.toOrdered D)
      (fun c => copiedKeyColumn p.root.column (block * (front.length - p.root.column)) c.val)

theorem Preparation.splice_boundary_key_bound
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    (block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1))))
    (hColumn : edge.lower.1.val = (p.spliceMountain hLast block).size)
    (D : Nat) (hDimension : MountainKeyDimension p.initial D) :
    Nonempty (BoundaryKeyBound p hLast block edge D) := by
  have hPhysicalColumn : edge.lower.1.val =
      front.length + block * (front.length - p.root.column) := by
    rw [hColumn, p.spliceMountain_size]
    rfl
  by_cases hZero : block = 0
  · subst block
    have hPreserved : PreservesColumns p.reduced (p.spliceMountain hLast 1) := by
      simpa only [p.physicalBlock_zero] using p.physicalBlock_preserved_next_graph hLast 0
    have hSourceBound : edge.lower.1.val < p.reduced.size := by
      rw [p.reduced_size_eq]
      omega
    obtain ⟨source, hEdge⟩ := hPreserved.storedEdge_preimage
      (p.spliceMountain_valid hLast 1).toOrdered edge hSourceBound
    have hMapped := congrArg (fun e => e.lower.1.val) hEdge
    have hSource : source.lower.1.val = front.length := by
      have hSame : (hPreserved.storedEdge source).lower.1.val = source.lower.1.val :=
        hPreserved.mapNode_column source.lower
      rw [hSame] at hMapped
      omega
    have hParent : edge.parent.1.val = source.parent.1.val := by
      rw [← hEdge]
      exact hPreserved.mapNode_column source.parent
    have hEval := hPreserved.storedEdge_key_eval (Label := Nat)
      p.reduced_valid.toOrdered (p.spliceMountain_valid hLast 1).toOrdered source D
      (fun c => c.val)
    rw [hEdge] at hEval
    change Keys.eval (edge.keyTemplate (p.spliceMountain_valid hLast 1).toOrdered D)
        (fun c => c.val) = Keys.eval (source.keyTemplate p.reduced_valid.toOrdered D)
        (fun c => c.val) at hEval
    refine ⟨⟨source, hSource, ?_, ?_⟩⟩
    · simpa only [Nat.zero_mul, copiedKeyColumn, Nat.add_zero, ite_self] using hParent
    · simpa only [Nat.zero_mul, copiedKeyColumn, Nat.add_zero, ite_self] using hEval.le
  · have hCopied : p.reduced.size ≤ edge.lower.1.val := by
      rw [p.reduced_size_eq]
      have hWidth : 0 < front.length - p.root.column := Nat.sub_pos_of_lt p.root_before_last
      have hProduct : 0 < block * (front.length - p.root.column) :=
        Nat.mul_pos (Nat.pos_of_ne_zero hZero) hWidth
      omega
    obtain ⟨bound⟩ := p.copied_edge_key_bound hLast (by omega : 0 < block + 1)
      (p.expandDiagram_eq_spliceMountain_all hLast (block + 1)) edge hCopied D
      (p.spliceMountain_key_dimension hLast hDimension (block + 1))
    obtain ⟨hBlock, hSource⟩ := bound.boundary_coordinates hPhysicalColumn
    refine ⟨⟨bound.source, hSource, ?_, ?_⟩⟩
    · simpa only [hBlock, p.reduced_block_width] using bound.parent_column
    · simpa only [hBlock, p.reduced_block_width] using bound.key_le

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ActualCopiedKeyBound.boundary_coordinates
#print axioms OmegaY.Expansion.Preparation.splice_boundary_key_bound
