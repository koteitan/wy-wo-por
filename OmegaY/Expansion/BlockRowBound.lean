/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlockRowBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.DynamicRowBound
import OmegaY.Expansion.BlockTotal

/-!
# Row bounds through the actual complete inner block loop

The invariant is carried by the real forIn over List.range width. Every
new column is bounded using the current DynamicBlockState and its fresh
reference map. No bound on the completed block is assumed.
-/

namespace OmegaY.Expansion

open Canonical

theorem BlockReady.copyBlock_rows_bound {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain}
    (ready : BlockReady p block start) (hLast : 1 < last) {height : Row}
    (hStartBound : MountainRowsBound start height)
    (hReducedBound : MountainRowsBound p.reduced height) (hLastTop : p.lastTop.row ≤ height)
    {result : Mountain}
    (hCopy : OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
      (p.reduced.size - 1 - p.root.column) block = .ok result) :
    MountainRowsBound result height := by
  let width := p.reduced.size - 1 - p.root.column
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRoot := p.root_before_last
  obtain ⟨references, hMap, hInitial⟩ := p.dynamic_block_init hLast ready.base_preserved
    ready.valid ready.size_eq ready.boundary_rows ready.boundary_power
  let body : Nat → Mountain → Result (ForInStep Mountain) := fun offset ambient => do
    let sourceColumn := p.root.column + offset + 1
    if ambient.size ≠ sourceColumn + block * width then throw .misplacedFill
    let column ← copyColumn ambient p.marked references sourceColumn (block * width) p.root.column
    return .yield (ambient.push column)
  let P : Nat → Mountain → Prop := fun offset ambient =>
    DynamicBlockState p block start references (p.root.column + offset + 1) ambient ∧
      MountainRowsBound ambient height
  have hInit : P 0 start := ⟨by simpa only [Nat.add_zero] using hInitial, hStartBound⟩
  have hStep : ∀ offset, offset < width → ∀ ambient, P offset ambient →
      ∃ next, body offset ambient = .ok (.yield next) ∧ P (offset + 1) next := by
    intro offset hOffset ambient hState
    have hNext : p.root.column + offset + 1 < p.reduced.size := by
      dsimp only [width] at hOffset
      omega
    obtain ⟨column, hRun, _, _, _, _, hPush, _⟩ := hState.1.copy_next hLast hNext
    have hBound := hState.1.copy_next_push_rows_bound hLast hNext hReducedBound hLastTop hState.2 hRun
    refine ⟨ambient.push column, ?_, ?_, hBound⟩
    · have hAmbientSize := hState.1.size_eq
      simp only [body, width, hAmbientSize, ne_eq, not_true_eq_false, ↓reduceIte, hRun]
      rfl
    · simpa only [Nat.add_assoc] using hPush
  obtain ⟨output, hRun, hFinal⟩ := forIn_range_indexed width start body P hInit hStep
  have hBuilt : OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
      (p.reduced.size - 1 - p.root.column) block = .ok output := by
    unfold OmegaY.Expansion.copyBlock
    rw [hMap]
    change (forIn (List.range width) start body >>= pure) = .ok output
    rw [hRun]
    rfl
  have hEq : output = result := Except.ok.inj (hBuilt.symm.trans hCopy)
  exact hEq ▸ hFinal.2

/-- Complete block success, next-block readiness, and the unchanged fixed
height bound are established simultaneously for the actual returned mountain. -/
theorem BlockReady.copyBlock_bounded {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain}
    (ready : BlockReady p block start) (hLast : 1 < last) {height : Row}
    (hStartBound : MountainRowsBound start height)
    (hReducedBound : MountainRowsBound p.reduced height) (hLastTop : p.lastTop.row ≤ height) :
    ∃ result,
      OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result ∧ MountainRowsBound result height := by
  obtain ⟨result, hRun, hReady⟩ := ready.copyBlock hLast
  exact ⟨result, hRun, hReady,
    ready.copyBlock_rows_bound hLast hStartBound hReducedBound hLastTop hRun⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.BlockReady.copyBlock_rows_bound
#print axioms OmegaY.Expansion.BlockReady.copyBlock_bounded
