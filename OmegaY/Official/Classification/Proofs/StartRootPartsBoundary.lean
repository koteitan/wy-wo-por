import OmegaY.Official.Classification.Proofs.StartRootPartsB0

/-!
# `BoundaryChain` from a step statement for the copies of `x₀`

`BoundaryChain` (`ChainCorrStartRoot.lean`) asks: the scale-`k` chain of a node `b` of the
boundary column `x₀ + w·(i - 1)` of block `i` (the copy of `x₀` made by block `i - 1`)
reaches every node left of `cr` that the chain of its origin `ν` reaches in `M(s)`.

* `i = 1`: proved (`boundaryChain_one`, `StartRootPartsB0.lean`).
* `i ≥ 2`: the copy of `x₀` is made by a block `m = i - 1 ≥ 1`, whose inner columns are the
  copies of `StepInner`. For a node `b` that is not a gap copy, one step `ν → m'` of the
  chain of `M(s)` from its origin is matched by the chain of `b` (`NextL`, with the copy
  relation `CopyNode` of block `m`):
  - upper part: proved (`upper_nextL`; `b` has the raw parent of `ν`);
  - lower part: the open statement `BoundaryStepLower` (the `StepInner`-type statement for the
    column `x₀`);
  and later steps from copy nodes are matched by `StepInner` (a hypothesis, open).
  For a gap copy `b`, the chain of `b` passes through gap copies of the inner columns, whose
  steps are not described by `StepInner`; this case is the open statement
  `BoundaryCutChain` (`BoundaryChain` restricted to gap copies).

`boundaryChain_of_parts`: `BoundaryChain` from `StepInner`, `BoundaryStepLower` and
`BoundaryCutChain`.

## Numerical tests

`reference/official/start-root-parts.cjs` (counts: node-scale pairs for
`BoundaryStepLower`, node-scale-target triples for `BoundaryCutChain`); no failure:

| sample | `BoundaryStepLower` | `BoundaryCutChain` |
|---|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 1296123 | 1119982 |
| legal, length ≤ 6, entries ≤ 6 | 235539 | 0 |
| legal, length ≤ 5, entries ≤ 8 | 180690 | 1404 |
| random legal (`--random 20000,10,10,7`) | 778320 | 9756 |
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-- (open) **One step from a lower node of a copy of `x₀`** in a block `m ≥ 1` that is not a
gap copy: the step `ν → m'` of the chain of `M(s)` from its origin is matched by the chain of
the node, with the copy nodes of block `m`. -/
def BoundaryStepLower : Prop :=
  ∀ s n D M out ρ R t, SpliceData s n D M out ρ R t → ∀ m, 0 < m → m < n →
    ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length), esB[k].2.isUpper = false → cutOrigin esB[k].2 = false →
      ∀ kk m', MStep M kk esB[k].2.src m' →
        NextL R M kk ρ.cr (CopyNode M R n ρ.cr ρ.x0 (official t.row) m)
          ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩ m'

/-- (open) **`BoundaryChain` for gap copies** of a block `m ≥ 1`. -/
def BoundaryCutChain : Prop :=
  ∀ s n D M out ρ R t, SpliceData s n D M out ρ R t → ∀ m, 0 < m → m < n →
    ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length), cutOrigin esB[k].2 = true →
      ∀ kk (p : Ref), p.column < ρ.cr → ScaleReach M kk esB[k].2.src p →
        ScaleReach R kk ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩ p

/-- `StepInner` as the step hypothesis of `reach_of_first`. -/
theorem stepInner_nextL (hStep : StepInner) {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t)
    {m : Nat} (hm0 : 0 < m) (hm : m < n + 1) (kk : Nat) :
    ∀ v p p', CopyNode M R n ρ.cr ρ.x0 (official t.row) m v p → MStep M kk p p' →
      NextL R M kk ρ.cr (CopyNode M R n ρ.cr ρ.x0 (official t.row) m) v p' := by
  intro v p p' hcp hst
  obtain ⟨col, hcol, ht⟩ := hd.last
  exact nextL_of_next (hStep s n D M out ρ R col t hd.splice hd.deg hd.run hd.canon hcol ht m
    hm0 hm v p hcp kk p' hst)

/-- **`BoundaryChain` from the step statements.** -/
theorem boundaryChain_of_parts (hStep : StepInner) (hBL : BoundaryStepLower)
    (hBC : BoundaryCutChain) : BoundaryChain := by
  intro s n D M out ρ R t hd i hi0 hin esB hes k hk kk p hp hr
  obtain ⟨_, hcrx, hinv, _⟩ := spliceData_facts hd
  have hA := hinv.1
  rcases Nat.lt_or_ge i 2 with hi1 | hi2
  · -- block `0`
    have hi : i - 1 = 0 := by omega
    rw [hi] at hes ⊢
    exact boundaryChain_one hd hes hk hp hr
  · have hm0 : 0 < i - 1 := by omega
    have hm : i - 1 < n := by omega
    cases hcut : cutOrigin esB[k].2
    · have hcr : ρ.cr ≤ esB[k].2.src.column := by
        have := (bsrc hes hk).1
        split at this <;> omega
      refine reach_of_first hA hcrx.le _ (stepInner_nextL hStep hd hm0 (by omega) kk) hr _ hcr
        ?_ hp
      intro m' hst
      cases hν : esB[k].2 with
      | upper ν =>
          rw [hν] at hst
          exact upper_nextL hd hm hes hk hν hst _
      | plain ν =>
          exact hBL s n D M out ρ R t hd (i - 1) hm0 hm esB hes k hk (by rw [hν]; rfl) hcut kk m'
            hst
      | clean ν b =>
          exact hBL s n D M out ρ R t hd (i - 1) hm0 hm esB hes k hk (by rw [hν]; rfl) hcut kk m'
            hst
    · exact hBC s n D M out ρ R t hd (i - 1) hm0 hm esB hes k hk hcut kk p hp hr

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts
