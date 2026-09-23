/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BlocksRawGeometry.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.BlockRawGeometry
import OmegaY.Expansion.LoopPrefix

/-!
# Raw stored-edge geometry through every actual expansion block

Induction on the finite copy count retains the actual prefix execution
equation. Consequently each next block has the genuine start-run premise
used by the high-parent selector; no arbitrary state is substituted for
an executable prefix. Numerical first-smaller recovery is not asserted.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Every finite collection of complete copied blocks has raw row
geometry. Source geometry is derived from the actual canonical build. -/
theorem Preparation.blocks_raw_geometry {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat) :
    ∃ result,
      (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result ∧ MountainRawGeometry result := by
  have hSizes : p.initial.size = p.reduced.size := by
    have hInitial := build_size p.initial_build
    have hReduced := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hInitial hReduced
    exact hInitial.trans hReduced.symm
  induction copies with
  | zero =>
    exact ⟨p.reduced, rfl, p.initial_block_ready hLast,
      mountainRawGeometry_of_normal (build_normal_of_success p.reduced_build)⟩
  | succ copies ih =>
    obtain ⟨start, hPrefix, hReady, hRaw⟩ := ih
    obtain ⟨result, hCopy, hNext, hResultRaw⟩ :=
      hReady.copyBlock_raw_geometry hLast hPrefix hRaw
    have hStep : copyBlock start p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (copies + 1) = .ok result := by
      simpa only [hSizes] using hCopy
    exact ⟨result, forIn_yield_range_succ p.reduced
      (fun block mountain => copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)) hPrefix hStep, hNext, hResultRaw⟩

/-- Determinism transfers the constructed invariant to any actual result
of this outer loop. -/
theorem Preparation.blocks_raw_geometry_of_run {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    MountainRawGeometry result := by
  obtain ⟨output, hOutput, _, hRaw⟩ := p.blocks_raw_geometry hLast copies
  have he : output = result := Except.ok.inj (hOutput.symm.trans hRun)
  exact he ▸ hRaw

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_raw_geometry
#print axioms OmegaY.Expansion.Preparation.blocks_raw_geometry_of_run
