/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlockBottomLegs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BottomLegCopy
import OmegaY.Expansion.BlockTotal

/-! Exact bottom-leg preservation through a complete actual copy block.
The inner indexed invariant tracks the real dynamic block state alongside
the old and appended bottom legs. Every appended endpoint is derived from
the canonical source bottom, never postulated for a copied output. -/

namespace OmegaY.Canonical

theorem BottomLegs.push_exact {mountain : Mountain} {column : Column}
    (hLegs : BottomLegs mountain) (hNonempty : 0 < mountain.size)
    {bottom : Cell} (hBottom : column[1]? = some bottom)
    (hLeft : bottom.left = some ⟨mountain.size - 1, 0⟩) :
    BottomLegs (mountain.push column) := by
  intro c hc
  by_cases he : c = mountain.size
  · subst c
    exact ⟨bottom, by simpa only [Array.getElem_push_eq] using hBottom,
      by simpa only [if_neg (Nat.ne_of_gt hNonempty)] using hLeft⟩
  · have hOld : c < mountain.size := by simp only [Array.size_push] at hc; omega
    simpa only [Array.getElem_push_lt hOld] using hLegs c hOld

theorem BottomLegs.pop {mountain : Mountain} (hLegs : BottomLegs mountain) :
    BottomLegs mountain.pop := by
  intro c hc
  have hOld : c < mountain.size := by simp only [Array.size_pop] at hc; omega
  simpa only [Array.getElem_pop hc] using hLegs c hOld

end OmegaY.Canonical

namespace OmegaY.Expansion

open Canonical

theorem DynamicBlockState.copy_next_bottom_left {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) (hNext : next < p.reduced.size) {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ bottom, column[1]? = some bottom ∧ bottom.left = some ⟨ambient.size - 1, 0⟩ := by
  obtain ⟨d, _, _, _⟩ := s.column_data hLast hNext
  have hBaseSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  exact d.copyColumn_bottom_left_of_build p.reduced_build hBaseSource s.next_lower hRun

theorem DynamicBlockState.copy_next_push_bottom_legs {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) (hNext : next < p.reduced.size) (hLegs : BottomLegs ambient)
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    BottomLegs (ambient.push column) := by
  obtain ⟨bottom, hBottom, hLeft⟩ := s.copy_next_bottom_left hLast hNext hRun
  have hNonempty : 0 < ambient.size := by have := s.size_eq; have := s.next_lower; omega
  exact hLegs.push_exact hNonempty hBottom hLeft

theorem BlockReady.copyBlock_bottom_legs {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain}
    (ready : BlockReady p block start) (hLast : 1 < last) (hStartLegs : BottomLegs start)
    {result : Mountain}
    (hCopy : OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
      (p.reduced.size - 1 - p.root.column) block = .ok result) :
    BottomLegs result := by
  let width := p.reduced.size - 1 - p.root.column
  obtain ⟨references, hMap, hInitial⟩ := p.dynamic_block_init hLast ready.base_preserved
    ready.valid ready.size_eq ready.boundary_rows ready.boundary_power
  let body : Nat → Mountain → Result (ForInStep Mountain) := fun offset ambient => do
    let sourceColumn := p.root.column + offset + 1
    if ambient.size ≠ sourceColumn + block * width then throw .misplacedFill
    let column ← copyColumn ambient p.marked references sourceColumn (block * width) p.root.column
    return .yield (ambient.push column)
  let P : Nat → Mountain → Prop := fun offset ambient =>
    DynamicBlockState p block start references (p.root.column + offset + 1) ambient ∧
      BottomLegs ambient
  have hInit : P 0 start := ⟨by simpa only [Nat.add_zero] using hInitial, hStartLegs⟩
  have hStep : ∀ offset, offset < width → ∀ ambient, P offset ambient →
      ∃ next, body offset ambient = .ok (.yield next) ∧ P (offset + 1) next := by
    intro offset hOffset ambient hState
    have hNext : p.root.column + offset + 1 < p.reduced.size := by
      dsimp only [width] at hOffset
      omega
    obtain ⟨column, hRun, _, _, _, _, hPush, _⟩ := hState.1.copy_next hLast hNext
    have hLegs := hState.1.copy_next_push_bottom_legs hLast hNext hState.2 hRun
    refine ⟨ambient.push column, ?_, ?_, hLegs⟩
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

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.copy_next_bottom_left
#print axioms OmegaY.Expansion.BlockReady.copyBlock_bottom_legs
