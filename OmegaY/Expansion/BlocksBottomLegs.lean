/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlocksBottomLegs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BlockBottomLegs
import OmegaY.Expansion.BlocksTotal

/-! Bottom legs throughout every finite number of actual copy blocks and
the final cut. References are selected freshly by each real block call;
the invariant retains the actual old columns and exact new bottom legs. -/

namespace OmegaY.Expansion

open Canonical

theorem Preparation.blocks_bottom_legs {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat) {result : Mountain}
    (hBlocks : (forIn (List.range copies) p.reduced (fun block ambient => do
      let next ← copyBlock ambient p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    BottomLegs result := by
  have hSizes : p.initial.size = p.reduced.size := by
    have hInitial := build_size p.initial_build
    have hReduced := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hInitial hReduced
    exact hInitial.trans hReduced.symm
  let body : Nat → Mountain → Result (ForInStep Mountain) := fun block ambient => do
    let next ← copyBlock ambient p.marked p.boundaries p.root.column
      (p.initial.size - 1 - p.root.column) (block + 1)
    pure (.yield next)
  let P : Nat → Mountain → Prop := fun block ambient =>
    BlockReady p (block + 1) ambient ∧ BottomLegs ambient
  have hInit : P 0 p.reduced :=
    ⟨p.initial_block_ready hLast, build_bottom_legs p.reduced_build⟩
  have hStep : ∀ block, block < copies → ∀ ambient, P block ambient →
      ∃ next, body block ambient = .ok (.yield next) ∧ P (block + 1) next := by
    intro block _ ambient hState
    obtain ⟨next, hRun, hReady⟩ := hState.1.copyBlock hLast
    have hLegs := hState.1.copyBlock_bottom_legs hLast hState.2 hRun
    refine ⟨next, ?_, hReady, hLegs⟩
    simp only [body, hSizes, hRun]
    rfl
  obtain ⟨output, hRun, hFinal⟩ := forIn_range_indexed copies p.reduced body P hInit hStep
  have hEq : output = result := Except.ok.inj (hRun.symm.trans hBlocks)
  exact hEq ▸ hFinal.2

/-- This is the returned diagram's bottom-leg invariant for the actual
positive-copy expansion, including deletion of its temporary last column. -/
theorem Preparation.expandDiagram_bottom_legs {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : Mountain} (hRun : expandDiagram (front ++ [last]) copies = .ok result) :
    BottomLegs result := by
  obtain ⟨full, hBlocks, _⟩ := p.blocks_total hLast copies
  have hLegs := p.blocks_bottom_legs hLast copies hBlocks
  have hBuilt : expandDiagram (front ++ [last]) copies = .ok full.pop := by
    rw [p.expandDiagram_eq_blocks hLast hCopies, hBlocks]
    rfl
  have hEq : full.pop = result := Except.ok.inj (hBuilt.symm.trans hRun)
  exact hEq ▸ hLegs.pop

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_bottom_legs
#print axioms OmegaY.Expansion.Preparation.expandDiagram_bottom_legs
