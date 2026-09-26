/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSpliceEdgeOrigins.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualBlockSplice
import OmegaY.Expansion.PreservedEdgePreimage

/-! Every actual edge in the next splicing graph comes from a retained
graph column, the previous temporary boundary, or an actual ordinary
source-column copy. All copying witnesses and local edge preimages are
recovered from the program's finite execution history. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

inductive ActualSpliceEdgeOrigin {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1)))) : Prop
  | retained (oldEdge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast block)))
      (hEdge : (p.spliceMountain_preserved_next hLast block).storedEdge oldEdge = edge)
  | boundary (oldEdge : RealStoredEdge (Frame.ofMountain (p.physicalBlock hLast block)))
      (hColumn : oldEdge.lower.1.val = (p.physicalBlock hLast block).size - 1)
      (hEdge : (p.physicalBlock_preserved_next_graph hLast block).storedEdge oldEdge = edge)
  | ordinary (sourceColumn : Nat) (before : Mountain) (column : Column) (references : List Ref)
      (state : DynamicBlockState p (block + 1) (p.physicalBlock hLast block)
        references sourceColumn before)
      (history : CopyRunHistory p (block + 1) (p.physicalBlock hLast block)
        references sourceColumn before)
      (hSourceLower : p.root.column < sourceColumn) (hSourceUpper : sourceColumn < front.length)
      (hCopy : copyColumn before p.marked references sourceColumn
        ((block + 1) * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
      (preserved : PreservesColumns (before.push column) (p.spliceMountain hLast (block + 1)))
      (oldEdge : RealStoredEdge (Frame.ofMountain (before.push column)))
      (hColumn : oldEdge.lower.1.val = before.size)
      (hEdge : preserved.storedEdge oldEdge = edge)

theorem Preparation.spliceMountain_edge_origin
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    (block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.spliceMountain hLast (block + 1)))) :
    ActualSpliceEdgeOrigin p hLast block edge := by
  have hOrdered := (p.spliceMountain_valid hLast (block + 1)).toOrdered
  by_cases hOld : edge.lower.1.val < (p.spliceMountain hLast block).size
  · obtain ⟨oldEdge, hEdge⟩ := (p.spliceMountain_preserved_next hLast block).storedEdge_preimage
      hOrdered edge hOld
    exact .retained oldEdge hEdge
  rcases p.spliceMountain_new_column_cases hLast block edge.lower.1.val
    (Nat.le_of_not_gt hOld) edge.lower.1.isLt with hBoundary | ⟨sourceColumn, hLower, hUpper, hColumn⟩
  · let preserved := p.physicalBlock_preserved_next_graph hLast block
    have hWidth : 0 < (p.physicalBlock hLast block).size := by rw [p.physicalBlock_size]; omega
    obtain ⟨oldEdge, hEdge⟩ := preserved.storedEdge_preimage hOrdered edge (by omega)
    have hMapped : (preserved.storedEdge oldEdge).lower.1.val = edge.lower.1.val :=
      congrArg (fun actual => actual.lower.1.val) hEdge
    have hOldColumn : oldEdge.lower.1.val = (p.physicalBlock hLast block).size - 1 :=
      (preserved.mapNode_column oldEdge.lower).symm.trans (hMapped.trans hBoundary)
    exact .boundary oldEdge hOldColumn hEdge
  · obtain ⟨references, _, _, _state, history⟩ := p.physicalBlock_step_history hLast block
    have hSourceBound : sourceColumn < p.reduced.size := by rw [p.reduced_size_eq]; omega
    obtain ⟨before, column, state, oldHistory, hCopy, hPreserved, _⟩ :=
      history.column_with_history hLower hSourceBound
    have hKept : (before.push column).size ≤ (p.physicalBlock hLast (block + 1)).size - 1 := by
      rw [Array.size_push, state.size_eq, p.physicalBlock_size, p.reduced_block_width]
      unfold Splice.blockWidth
      omega
    let preserved : PreservesColumns (before.push column) (p.spliceMountain hLast (block + 1)) :=
      hPreserved.pop_of_size hKept
    have hDestination : edge.lower.1.val = before.size := hColumn.trans state.size_eq.symm
    obtain ⟨oldEdge, hEdge⟩ := preserved.storedEdge_preimage hOrdered edge
      (by simp only [Array.size_push]; omega)
    have hMapped : (preserved.storedEdge oldEdge).lower.1.val = edge.lower.1.val :=
      congrArg (fun actual => actual.lower.1.val) hEdge
    have hOldColumn : oldEdge.lower.1.val = before.size :=
      (preserved.mapNode_column oldEdge.lower).symm.trans (hMapped.trans hDestination)
    exact .ordinary sourceColumn before column references state oldHistory hLower hUpper
      hCopy preserved oldEdge hOldColumn hEdge

/-- The boundary left by a positive physical block is exactly its real
copy of source x. This recovers the actual local execution and all parent
columns for applying an edge-key theorem to a later boundary edge. -/
theorem Preparation.physicalBlock_boundary_edge_run
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    (block : Nat)
    (edge : RealStoredEdge (Frame.ofMountain (p.physicalBlock hLast (block + 1))))
    (hColumn : edge.lower.1.val = (p.physicalBlock hLast (block + 1)).size - 1) :
    ∃ before column references,
      ∃ _state : DynamicBlockState p (block + 1) (p.physicalBlock hLast block)
        references front.length before,
      CopyRunHistory p (block + 1) (p.physicalBlock hLast block) references front.length before ∧
      copyColumn before p.marked references front.length
        ((block + 1) * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column ∧
      ∃ preserved : PreservesColumns (before.push column) (p.physicalBlock hLast (block + 1)),
      ∃ oldEdge : RealStoredEdge (Frame.ofMountain (before.push column)),
        before.size = (p.physicalBlock hLast (block + 1)).size - 1 ∧
        oldEdge.lower.1.val = before.size ∧ preserved.storedEdge oldEdge = edge := by
  obtain ⟨references, _, _, _state, history⟩ := p.physicalBlock_step_history hLast block
  have hSourceBound : front.length < p.reduced.size := by rw [p.reduced_size_eq]; omega
  obtain ⟨before, column, state, oldHistory, hCopy, preserved, _⟩ :=
    history.column_with_history p.root_before_last hSourceBound
  have hDestination : before.size = (p.physicalBlock hLast (block + 1)).size - 1 := by
    rw [state.size_eq, p.physicalBlock_size, p.reduced_block_width]
    unfold Splice.blockWidth
    omega
  obtain ⟨oldEdge, hEdge⟩ := preserved.storedEdge_preimage
    (p.physicalBlock_ready hLast (block + 1)).valid.toOrdered edge
    (by simp only [Array.size_push]; omega)
  have hMapped : (preserved.storedEdge oldEdge).lower.1.val = edge.lower.1.val :=
    congrArg (fun actual => actual.lower.1.val) hEdge
  have hOldColumn : oldEdge.lower.1.val = before.size :=
    (preserved.mapNode_column oldEdge.lower).symm.trans
      (hMapped.trans (hColumn.trans hDestination.symm))
  exact ⟨before, column, references, state, oldHistory, hCopy, preserved, oldEdge,
    hDestination, hOldColumn, hEdge⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.spliceMountain_edge_origin
#print axioms OmegaY.Expansion.Preparation.physicalBlock_boundary_edge_run
