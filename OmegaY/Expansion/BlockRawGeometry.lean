/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlockRawGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRawGeometry
import OmegaY.Expansion.RawFrameGeometry

/-!
# Raw geometry through the complete actual inner copy loop

The invariant retains the current dynamic state, the actual history of
earlier column executions, and raw geometry for the entire current
mountain. Each new column is certified by the executable adjacency
classification and appended by the reference-level preservation theorem.
The block-start run is a real prefix of the outer expansion loop.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A complete block preserves raw geometry and returns its actual column
history. The incoming raw property is the induction hypothesis for the
previous mountain, not an assumption on newly copied columns. -/
theorem BlockReady.copyBlock_with_raw_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start : Mountain}
    (ready : BlockReady p block start) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← OmegaY.Expansion.copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    (hRaw : MountainRawGeometry start) :
    ∃ result references,
      OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result ∧
      p.boundaries.mapM (below start (start.size - 1)) = .ok references ∧
      DynamicBlockState p block start references p.reduced.size result ∧
      CopyRunHistory p block start references p.reduced.size result ∧
      MountainRawGeometry result := by
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
      CopyRunHistory p block start references (p.root.column + offset + 1) ambient ∧
      MountainRawGeometry ambient
  have hInit : P 0 start := by
    exact ⟨by simpa only [Nat.add_zero] using hInitial,
      by simpa only [Nat.add_zero] using CopyRunHistory.initial p block start references,
      hRaw⟩
  have hStep : ∀ offset, offset < width → ∀ ambient, P offset ambient →
      ∃ next, body offset ambient = .ok (.yield next) ∧ P (offset + 1) next := by
    intro offset hOffset ambient hState
    have hNext : p.root.column + offset + 1 < p.reduced.size := by
      dsimp only [width] at hOffset
      omega
    obtain ⟨column, hRun, hValid, _, _, _, hPush, _⟩ := hState.1.copy_next hLast hNext
    have hNew : ∀ index lower upper, column[index]? = some lower →
        column[index + 1]? = some upper → 0 < index → CopiedRawAt ambient column lower upper := by
      intro index lower upper hLower hUpper hReal
      have hPositive := hValid.rows_strict 0 index phantom lower hValid.phantom hLower hReal
      have hNonzero : lower.row ≠ 0 := by
        change (0 : Row) < lower.row at hPositive
        exact ne_of_gt hPositive
      exact hState.1.actual_adjacent_raw_geometry hState.2.1 hLast hStartRun hNext hRun
        hLower hUpper hNonzero
    refine ⟨ambient.push column, ?_, ?_, ?_, hState.2.2.push hNew⟩
    · have hAmbientSize := hState.1.size_eq
      simp only [body, width, hAmbientSize, ne_eq, not_true_eq_false, ↓reduceIte, hRun]
      rfl
    · simpa only [Nat.add_assoc] using hPush
    · simpa only [Nat.add_assoc] using CopyRunHistory.push hState.2.1 hState.1 hRun
  obtain ⟨result, hRun, hFinal⟩ := forIn_range_indexed width start body P hInit hStep
  have hEnd : p.root.column + width + 1 = p.reduced.size := by dsimp only [width]; omega
  have hResult : OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column width block = .ok result := by
    unfold OmegaY.Expansion.copyBlock
    rw [hMap]
    change (forIn (List.range width) start body >>= pure) = .ok result
    rw [hRun]
    rfl
  obtain ⟨checked, hChecked, hReady⟩ := ready.copyBlock hLast
  have he : checked = result := Except.ok.inj (hChecked.symm.trans hResult)
  subst checked
  exact ⟨result, references, hResult, hReady, hMap,
    by simpa only [hEnd] using hFinal.1,
    by simpa only [hEnd] using hFinal.2.1, hFinal.2.2⟩

/-- Concise block-level interface, keeping the real execution equation,
next-block readiness, and raw geometry. -/
theorem BlockReady.copyBlock_raw_geometry
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start : Mountain}
    (ready : BlockReady p block start) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← OmegaY.Expansion.copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    (hRaw : MountainRawGeometry start) :
    ∃ result,
      OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result ∧ MountainRawGeometry result := by
  obtain ⟨result, _, hRun, hReady, _, _, _, hResultRaw⟩ :=
    ready.copyBlock_with_raw_geometry hLast hStartRun hRaw
  exact ⟨result, hRun, hReady, hResultRaw⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.BlockReady.copyBlock_with_raw_geometry
#print axioms OmegaY.Expansion.BlockReady.copyBlock_raw_geometry
