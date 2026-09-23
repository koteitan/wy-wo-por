/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualBlockSplice.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CopyRunHistory
import OmegaY.Expansion.LoopPrefix
import OmegaY.Expansion.FinalHighEventSampling
import OmegaY.Expansion.DecrementGraftKeys
import OmegaY.Splice.BlockIndices

/-! The physical outer loop and the graphs used in finite splicing.
The graph after b blocks is the actual loop result with its temporary
last column removed. The next graph retains that boundary column and
adds exactly L-1 ordinary copied columns, also when L=1. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

namespace Preparation

variable {front : List Nat} {last : Nat} (p : Preparation front last)

noncomputable def physicalBlock (hLast : 1 < last) (block : Nat) : Mountain :=
  Classical.choose (p.blocks_total hLast block)

theorem physicalBlock_run (hLast : 1 < last) (block : Nat) :
    (forIn (List.range block) p.reduced (fun b ambient => do
      let next ← copyBlock ambient p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (b + 1)
      pure (.yield next)) : Result Mountain) = .ok (p.physicalBlock hLast block) :=
  (Classical.choose_spec (p.blocks_total hLast block)).1

theorem physicalBlock_ready (hLast : 1 < last) (block : Nat) :
    BlockReady p (block + 1) (p.physicalBlock hLast block) :=
  (Classical.choose_spec (p.blocks_total hLast block)).2

theorem physicalBlock_eq_of_run (hLast : 1 < last) {block : Nat} {result : Mountain}
    (hRun : (forIn (List.range block) p.reduced (fun b ambient => do
      let next ← copyBlock ambient p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (b + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    p.physicalBlock hLast block = result :=
  Except.ok.inj ((p.physicalBlock_run hLast block).symm.trans hRun)

@[simp] theorem physicalBlock_zero (hLast : 1 < last) :
    p.physicalBlock hLast 0 = p.reduced := p.physicalBlock_eq_of_run hLast rfl

noncomputable def spliceMountain (hLast : 1 < last) (block : Nat) : Mountain :=
  (p.physicalBlock hLast block).pop

theorem reduced_size_eq : p.reduced.size = front.length + 1 := by
  simpa only [List.length_append, List.length_singleton] using build_size p.reduced_build

theorem reduced_block_width : p.reduced.size - 1 - p.root.column = front.length - p.root.column := by
  rw [p.reduced_size_eq]
  omega

theorem physicalBlock_size (hLast : 1 < last) (block : Nat) :
    (p.physicalBlock hLast block).size = Splice.blockWidth front.length p.root.column block + 1 := by
  have h := (p.physicalBlock_ready hLast block).size_eq
  have hRoot := p.root_before_last
  rw [p.reduced_block_width, Nat.add_mul, Nat.one_mul] at h
  unfold Splice.blockWidth
  omega

theorem spliceMountain_size (hLast : 1 < last) (block : Nat) :
    (p.spliceMountain hLast block).size = Splice.blockWidth front.length p.root.column block := by
  simp only [spliceMountain, Array.size_pop, p.physicalBlock_size, Nat.add_sub_cancel]

theorem spliceMountain_valid (hLast : 1 < last) (block : Nat) :
    MountainValid (p.spliceMountain hLast block) :=
  (p.physicalBlock_ready hLast block).valid.pop

/-- Actual execution, fresh references, and all individual copy runs are
recovered from totality and deterministic agreement with the chosen loop
results. No transition or successful column is assumed by the caller. -/
theorem physicalBlock_step_history (hLast : 1 < last) (block : Nat) :
    ∃ references,
      copyBlock (p.physicalBlock hLast block) p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) (block + 1) =
          .ok (p.physicalBlock hLast (block + 1)) ∧
      p.boundaries.mapM (below (p.physicalBlock hLast block)
        ((p.physicalBlock hLast block).size - 1)) = .ok references ∧
      DynamicBlockState p (block + 1) (p.physicalBlock hLast block) references
        p.reduced.size (p.physicalBlock hLast (block + 1)) ∧
      CopyRunHistory p (block + 1) (p.physicalBlock hLast block) references
        p.reduced.size (p.physicalBlock hLast (block + 1)) := by
  obtain ⟨result, references, hCopy, _, hMap, state, history⟩ :=
    (p.physicalBlock_ready hLast block).copyBlock_with_history hLast
  have hSizes : p.initial.size = p.reduced.size := by
    rw [p.reduced_size_eq]
    simpa only [List.length_append, List.length_singleton] using build_size p.initial_build
  have hStep : copyBlock (p.physicalBlock hLast block) p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1) = .ok result := by
    simpa only [hSizes] using hCopy
  have hFull := forIn_yield_range_succ p.reduced
    (fun b ambient => copyBlock ambient p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (b + 1))
    (p.physicalBlock_run hLast block) hStep
  have he := p.physicalBlock_eq_of_run hLast hFull
  subst result
  exact ⟨references, hCopy, hMap, state, history⟩

theorem physicalBlock_preserved_next_graph (hLast : 1 < last) (block : Nat) :
    PreservesColumns (p.physicalBlock hLast block) (p.spliceMountain hLast (block + 1)) := by
  obtain ⟨_, _, _, state, _⟩ := p.physicalBlock_step_history hLast block
  apply state.start_preserved.pop_of_size
  rw [p.physicalBlock_size, p.physicalBlock_size, Splice.blockWidth_succ]
  have hRoot := p.root_before_last
  omega

theorem spliceMountain_preserved_next (hLast : 1 < last) (block : Nat) :
    PreservesColumns (p.spliceMountain hLast block) (p.spliceMountain hLast (block + 1)) :=
  (PreservesColumns.pop_prefix _).trans (p.physicalBlock_preserved_next_graph hLast block)

theorem spliceMountain_boundary_column (hLast : 1 < last) (block : Nat) :
    (p.physicalBlock hLast block).size - 1 =
      (p.spliceMountain hLast block).size := by
  simp only [spliceMountain, Array.size_pop]

theorem spliceMountain_new_width (hLast : 1 < last) (block : Nat) :
    (p.spliceMountain hLast (block + 1)).size - (p.spliceMountain hLast block).size =
      front.length - p.root.column := by
  rw [p.spliceMountain_size, p.spliceMountain_size, Splice.blockWidth_succ]
  omega

/-- Every new physical column is either the previously temporary boundary
or the next block's copy of one strict interior source column y<c<x. -/
theorem spliceMountain_new_column_cases (hLast : 1 < last) (block column : Nat)
    (hNew : (p.spliceMountain hLast block).size ≤ column)
    (hBound : column < (p.spliceMountain hLast (block + 1)).size) :
    column = (p.physicalBlock hLast block).size - 1 ∨
      ∃ sourceColumn, p.root.column < sourceColumn ∧ sourceColumn < front.length ∧
        column = sourceColumn + (block + 1) * (p.reduced.size - 1 - p.root.column) := by
  by_cases he : column = (p.spliceMountain hLast block).size
  · exact Or.inl (he.trans (p.spliceMountain_boundary_column hLast block).symm)
  right
  simp only [p.spliceMountain_size] at hNew hBound he
  rw [p.reduced_block_width]
  simp only [Splice.blockWidth, Nat.add_mul, Nat.one_mul] at hNew hBound he ⊢
  have hRoot := p.root_before_last
  refine ⟨column - ((block + 1) * (front.length - p.root.column)), ?_, ?_, ?_⟩ <;>
    simp only [Nat.add_mul, Nat.one_mul] <;> omega

theorem spliceMountain_unit_new_column (hLast : 1 < last) (block column : Nat)
    (hUnit : front.length - p.root.column = 1)
    (hNew : (p.spliceMountain hLast block).size ≤ column)
    (hBound : column < (p.spliceMountain hLast (block + 1)).size) :
    column = (p.physicalBlock hLast block).size - 1 := by
  rcases p.spliceMountain_new_column_cases hLast block column hNew hBound with h | ⟨c, hc, hx, _⟩
  · exact h
  · omega

/-- The semantic graph really is the program's final returned mountain
for every positive copy count; the chosen loop witness is not a surrogate
expansion rule. -/
theorem expandDiagram_eq_spliceMountain (hLast : 1 < last) {copies : Nat}
    (hCopies : 0 < copies) :
    expandDiagram (front ++ [last]) copies = .ok (p.spliceMountain hLast copies) :=
  p.expandDiagram_of_blocks hLast hCopies (p.physicalBlock_run hLast copies)

end Preparation
end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.physicalBlock_step_history
#print axioms OmegaY.Expansion.Preparation.physicalBlock_preserved_next_graph
#print axioms OmegaY.Expansion.Preparation.spliceMountain_new_column_cases
#print axioms OmegaY.Expansion.Preparation.spliceMountain_unit_new_column
#print axioms OmegaY.Expansion.Preparation.expandDiagram_eq_spliceMountain
