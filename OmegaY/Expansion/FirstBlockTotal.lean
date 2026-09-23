/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/FirstBlockTotal.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PreparedBlockRun
import OmegaY.Expansion.IndexedLoop

/-! The actual first copyBlock loop terminates successfully for every width
provided by a preparation. Its indexed invariant is advanced by the actual
column theorem; no whole-loop success is assumed. -/

namespace OmegaY.Expansion

open Canonical

theorem Preparation.first_block_with_references {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∃ result,
      copyBlock p.reduced p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) 1 = .ok result ∧
      PreparedBlockState p references p.reduced.size result := by
  let width := p.reduced.size - 1 - p.root.column
  let body : Nat → Mountain → Result (ForInStep Mountain) := fun offset ambient => do
    let sourceColumn := p.root.column + offset + 1
    if ambient.size ≠ sourceColumn + width then throw .misplacedFill
    let column ← copyColumn ambient p.marked references sourceColumn width p.root.column
    return .yield (ambient.push column)
  let P : Nat → Mountain → Prop := fun offset ambient =>
    PreparedBlockState p references (p.root.column + offset + 1) ambient
  have hInit : P 0 p.reduced := by
    simpa only [P, Nat.add_zero] using p.initial_block_state references
  have hStep : ∀ offset, offset < width → ∀ ambient, P offset ambient →
      ∃ next, body offset ambient = .ok (.yield next) ∧ P (offset + 1) next := by
    intro offset hOffset ambient hState
    have hNext : p.root.column + offset + 1 < p.reduced.size := by
      dsimp [width] at hOffset
      omega
    obtain ⟨column, hRun, _, _, _, _, _, hPush⟩ := hState.copy_next hLast hMap hNext
    refine ⟨ambient.push column, ?_, ?_⟩
    · have hSize := hState.size_eq
      simp only [body, width, hSize, ne_eq, not_true_eq_false, ↓reduceIte, hRun]
      rfl
    · simpa only [P, Nat.add_assoc] using hPush
  obtain ⟨result, hRun, hFinal⟩ :=
    forIn_range_indexed width p.reduced body P hInit hStep
  refine ⟨result, ?_, ?_⟩
  · unfold copyBlock
    have hSizes : p.initial.size = p.reduced.size := by
      have hInitial := build_size p.initial_build
      have hReduced := build_size p.reduced_build
      simp only [List.length_append, List.length_singleton] at hInitial hReduced
      exact hInitial.trans hReduced.symm
    rw [hSizes, hMap]
    simp only [Nat.one_mul]
    change (forIn (List.range width) p.reduced body >>= pure) = .ok result
    rw [hRun]
    rfl
  · have hEnd : p.root.column + width + 1 = p.reduced.size := by
      have hSize := build_size p.reduced_build
      simp only [List.length_append, List.length_singleton] at hSize
      have hRoot := p.root_before_last
      dsimp [width]
      omega
    simpa only [P, hEnd] using hFinal

theorem Preparation.first_block_total {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) :
    ∃ result,
      copyBlock p.reduced p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) 1 = .ok result ∧
      MountainValid result ∧ PreservesColumns p.reduced result ∧
      ∃ references, PreparedBlockState p references p.reduced.size result := by
  obtain ⟨references, hMap, _⟩ := p.initial_references hLast
  obtain ⟨result, hRun, hState⟩ := p.first_block_with_references hLast hMap
  exact ⟨result, hRun, hState.ambient_valid, hState.base_preserved, references, hState⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.first_block_with_references
#print axioms OmegaY.Expansion.Preparation.first_block_total
