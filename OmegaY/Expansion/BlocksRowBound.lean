/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlocksRowBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BlockRowBound
import OmegaY.Expansion.BlocksTotal

/-!
# One fixed row bound for arbitrarily many actual copied blocks

The indexed invariant follows the real outer forIn loop. References are
recomputed inside each copyBlock, but every selected cap is bounded by the
same original last-top row. The final pop preserves the bound. These are
finite-expansion bounds, not a proof of trajectory termination.
-/

namespace OmegaY.Expansion

open Canonical

theorem Preparation.blocks_bounded_of_reduced {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat) {height : Row}
    (hReducedBound : MountainRowsBound p.reduced height) (hLastTop : p.lastTop.row ≤ height) :
    ∃ result,
      (forIn (List.range copies) p.reduced (fun block ambient => do
        let next ← copyBlock ambient p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result ∧ MountainRowsBound result height := by
  have hSizes : p.initial.size = p.reduced.size := by
    have hInitial := build_size p.initial_build
    have hReduced := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hInitial hReduced
    exact hInitial.trans hReduced.symm
  apply forIn_range_indexed copies p.reduced _ (fun block ambient =>
    BlockReady p (block + 1) ambient ∧ MountainRowsBound ambient height)
  · exact ⟨p.initial_block_ready hLast, hReducedBound⟩
  · intro block _ ambient hState
    obtain ⟨result, hRun, hReady, hBound⟩ :=
      hState.1.copyBlock_bounded hLast hState.2 hReducedBound hLastTop
    refine ⟨result, ?_, hReady, hBound⟩
    rw [hSizes, hRun]
    rfl

/-- The caller need only bound the original input mountain. The exact
decrement supplies the reduced bound, and the original last top is an
actual node of that original mountain. -/
theorem Preparation.blocks_bounded {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat) {height : Row}
    (hInitialBound : MountainRowsBound p.initial height) :
    ∃ result,
      (forIn (List.range copies) p.reduced (fun block ambient => do
        let next ← copyBlock ambient p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result ∧ MountainRowsBound result height :=
  p.blocks_bounded_of_reduced hLast copies (p.reduced_rows_bound hLast hInitialBound)
    (p.lastTop_row_bound hInitialBound)

/-- Every finite copy count, including zero, produces a diagram below the
original mountain's row bound. The output is the real expandDiagram result. -/
theorem Preparation.expandDiagram_bounded {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat) {height : Row}
    (hInitialBound : MountainRowsBound p.initial height) :
    ∃ result, expandDiagram (front ++ [last]) copies = .ok result ∧
      MountainRowsBound result height := by
  by_cases hZero : copies = 0
  · subst copies
    refine ⟨p.initial.pop, ?_, hInitialBound.pop⟩
    simp [expandDiagram, p.initial_build, Except.mapError]
  · obtain ⟨result, hRun, _, hBound⟩ := p.blocks_bounded hLast copies hInitialBound
    refine ⟨result.pop, ?_, hBound.pop⟩
    rw [p.expandDiagram_eq_blocks hLast (Nat.pos_of_ne_zero hZero), hRun]
    rfl

theorem Preparation.expandDiagram_rows_bound {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} {height : Row}
    (hInitialBound : MountainRowsBound p.initial height) {result : Mountain}
    (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    MountainRowsBound result height := by
  obtain ⟨output, hOutput, hBound⟩ := p.expandDiagram_bounded hLast copies hInitialBound
  have hEq : output = result := Except.ok.inj (hOutput.symm.trans hRun)
  exact hEq ▸ hBound

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_bounded
#print axioms OmegaY.Expansion.Preparation.expandDiagram_bounded
#print axioms OmegaY.Expansion.Preparation.expandDiagram_rows_bound
