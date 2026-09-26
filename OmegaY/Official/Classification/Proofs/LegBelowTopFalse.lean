import OmegaY.Official.Classification.Proofs.ChainCorrStartLegJump

/-!
# `LegBelowTop` is false

`LegBelowTop` (`ChainCorrStartLegJump.lean`) says: in `M(s)` with top `t` of the last column
and root `r = left(t)` in column `c_r`, every node `u` of a column `c_r < c ≤ x₀` whose row is
below the row of `t` has its left end in a column `≥ c_r`.

It fails for `s = (1,2,4,8,10,8)`. The mountain, with stored rows (the bottom row is `1`)
and left ends:

```
column 0: 1
column 1: 1 ← (0,0),  2 ← (0,1)
column 2: 1 ← (1,0),  2 ← (1,1),  3 ← (1,2)
column 3: 1 ← (2,0),  2 ← (2,1),  3 ← (2,2),  4 ← (2,3)
column 4: 1 ← (3,0),  2 ← (3,1),  3 ← (1,2)
column 5: 1 ← (4,0),  2 ← (2,1),  3 ← (2,2),  4 ← (2,3)
```

The top `t = (5,4)` has row `4` and root `(2,3)`, so `c_r = 2`. The node `u = (4,3)` of
column `4` has row `3 < 4`, but its left end `(1,2)` is in column `1 < 2`.

The facts about the mountain are checked by `decide +kernel` (kernel evaluation of
`Canonical.build`, no `native_decide`).

How often it fails (`reference/official/legbelowtop-parts.cjs`, and the `LegBelowTop` count of
`reference/official/startleg-jump.cjs`, which reports the same failures): never for legal
inputs of length `≤ 7` with entries `≤ 9`, nor on the standard samples S1–S3, S6; in 64 of the
248831 legal inputs of length `≤ 6` with entries `≤ 12` (the shortest is `(1,3,9,11,9)`); in 20
of 75580 random legal inputs of length `≤ 7` with entries `≤ 12`. The general forms of the
statement for every edge (not only the top edge `t⁻ → r`) fail on the same inputs.

The same input also breaks `StartLeg` (`ChainCorrRegions.lean`) numerically:
`node reference/official/chain-corr.cjs --copies 1,2,3 FILE` with `FILE = [[1,2,4,8,10,8]]`
reports `FAIL StartLeg` at `(1,2,4,8,10,8)[1]`, `X = 7` (402 failures on the 64 inputs
above), while the classification itself holds there (`reserve.cjs --cand legOnly,leg
--top-control`: 0 failures) and so do `KeyLeShift` (`keylerest-regions.cjs`), `StartJump`,
`StartCopy`, `StartRoot` and `StepInner` (`chain-corr.cjs`). In every `StartLeg` failure the
origin is plain, the copy keeps its row, and the leg column has no node at that row.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegJump

open Canonical Reserve Official

/-- The counterexample input. -/
def cexInput : List Nat := [1, 2, 4, 8, 10, 8]

/-- The facts about `M(1,2,4,8,10,8)` used below: six columns; the top `t` of column `5` has
a real row and root `(2,3)`; the node `u = (4,3)` has a row below `t` and left end `(1,2)`. -/
def cexCheck (M : Mountain) : Bool :=
  M.size == 6 &&
    match (M[M.size - 1]?).bind Array.back?, cell? M ⟨4, 3⟩ with
    | some t, some u =>
        decide (official t.row ≠ 0) && decide (u.row < t.row) &&
          decide (t.left = some ⟨2, 3⟩) && decide (u.left = some ⟨1, 2⟩)
    | _, _ => false

/-- Kernel evaluation of the canonical build (no `native_decide`). -/
theorem cex_check : (Canonical.build cexInput).map cexCheck = .ok true := by
  decide +kernel

/-- **`LegBelowTop` is false** (counterexample `s = (1,2,4,8,10,8)`). -/
theorem not_legBelowTop : ¬ LegBelowTop := by
  intro h
  have hc0 := cex_check
  cases hb : Canonical.build cexInput with
  | error e =>
      rw [hb] at hc0
      cases hc0
  | ok M =>
      rw [hb] at hc0
      have hc : cexCheck M = true := by
        simpa only [Except.map, Except.ok.injEq] using hc0
      simp only [cexCheck, Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hsize, hc⟩ := hc
      split at hc
      · rename_i t u ht hu
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨hreal, hlt⟩, htl⟩, hul⟩ := hc
        have hTop : Recon.Top cexInput M t ⟨2, 3⟩ :=
          ⟨hb, ht, hreal, htl, by rw [hsize]; decide⟩
        have := h cexInput M t ⟨2, 3⟩ hTop ⟨4, 3⟩ u ⟨1, 2⟩ (by decide)
          (by rw [hsize]; decide) hu hul hlt
        exact absurd this (by decide)
      · cases hc

end OmegaY.Official.Classification.Proofs.ChainCorr.LegJump

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.not_legBelowTop
