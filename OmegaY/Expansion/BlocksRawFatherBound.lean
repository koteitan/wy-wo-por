/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlocksRawFatherBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BlockRawFatherBound
import OmegaY.Expansion.LoopPrefix

/-! Every finite number of actual complete blocks preserves raw D. The fresh
reference map and the current boundary are rebuilt at each block by readiness. -/

namespace OmegaY.Expansion

open Canonical Geometry

theorem Preparation.blocks_raw_father_bound {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat) :
    ∃ result,
      (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result ∧ MountainRawFatherBound result := by
  have hSizes : p.initial.size = p.reduced.size := by
    have hInitial := build_size p.initial_build
    have hReduced := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hInitial hReduced
    exact hInitial.trans hReduced.symm
  induction copies with
  | zero =>
    exact ⟨p.reduced, rfl, p.initial_block_ready hLast,
      mountainRawFatherBound_of_normal p.reduced_valid (build_normal_of_success p.reduced_build)⟩
  | succ copies ih =>
    obtain ⟨start, hPrefix, hReady, hBound⟩ := ih
    obtain ⟨result, hCopy, hNext, hResultBound⟩ := hReady.copyBlock_raw_father_bound hLast hBound
    have hStep : copyBlock start p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (copies + 1) = .ok result := by
      simpa only [hSizes] using hCopy
    exact ⟨result, forIn_yield_range_succ p.reduced
      (fun block mountain => copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)) hPrefix hStep, hNext, hResultBound⟩

theorem Preparation.blocks_raw_father_bound_of_run {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    MountainRawFatherBound result := by
  obtain ⟨output, hOutput, _, hBound⟩ := p.blocks_raw_father_bound hLast copies
  have he : output = result := Except.ok.inj (hOutput.symm.trans hRun)
  exact he ▸ hBound

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_raw_father_bound
#print axioms OmegaY.Expansion.Preparation.blocks_raw_father_bound_of_run
