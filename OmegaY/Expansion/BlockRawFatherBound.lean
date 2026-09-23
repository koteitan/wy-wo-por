/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlockRawFatherBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawFatherFrame
import OmegaY.Expansion.ActualCellFatherBound
import OmegaY.Expansion.BlockTotal

/-! Raw father-upper bounds through the actual inner loop. The old bound is
an induction hypothesis; each newly copied cell is certified from its own
execution. No numerical parent identification or copied Normal is used. -/

namespace OmegaY.Expansion

open Canonical Geometry

theorem BlockReady.copyBlock_raw_father_bound
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain}
    (ready : BlockReady p block start) (hLast : 1 < last)
    (hBound : MountainRawFatherBound start) :
    ∃ result,
      OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result ∧ MountainRawFatherBound result := by
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
      MountainRawFatherBound ambient
  have hInit : P 0 start :=
    ⟨by simpa only [Nat.add_zero] using hInitial, hBound⟩
  have hStep : ∀ offset, offset < width → ∀ ambient, P offset ambient →
      ∃ next, body offset ambient = .ok (.yield next) ∧ P (offset + 1) next := by
    intro offset hOffset ambient hState
    have hNext : p.root.column + offset + 1 < p.reduced.size := by
      dsimp only [width] at hOffset
      omega
    obtain ⟨column, hRun, hValid, _, _, _, hPush, _⟩ := hState.1.copy_next hLast hNext
    have hNew : ColumnRawFatherBound (ambient.push column) column := by
      intro index lower upper hLower hUpper hReal
      have hCell := hState.1.actual_copyColumn_father_bound hLast hNext hRun
        (index + 1) upper hUpper
      exact hCell.push column (fun ref hLeft => (hValid.stored_valid _ _ _ hUpper hLeft).1)
    refine ⟨ambient.push column, ?_, ?_, hState.2.push hState.1.ambient_valid hNew⟩
    · have hAmbientSize := hState.1.size_eq
      simp only [body, width, hAmbientSize, ne_eq, not_true_eq_false, ↓reduceIte, hRun]
      rfl
    · simpa only [Nat.add_assoc] using hPush
  obtain ⟨result, hRun, hFinal⟩ := forIn_range_indexed width start body P hInit hStep
  have hResult : OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column width block =
      .ok result := by
    unfold OmegaY.Expansion.copyBlock
    rw [hMap]
    change (forIn (List.range width) start body >>= pure) = .ok result
    rw [hRun]
    rfl
  obtain ⟨checked, hChecked, hReady⟩ := ready.copyBlock hLast
  have he : checked = result := Except.ok.inj (hChecked.symm.trans hResult)
  subst checked
  exact ⟨result, hResult, hReady, hFinal.2⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.BlockReady.copyBlock_raw_father_bound
