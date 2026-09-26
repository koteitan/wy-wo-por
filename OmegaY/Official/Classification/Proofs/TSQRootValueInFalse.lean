import OmegaY.Official.Classification.Proofs.TSQRootValueX0

set_option autoImplicit false

/-!
# `RootValueIn` is false (and so are `RootValueHi`, `RootValue` and `AscUp`)

`RootValueIn` (`TSQRootValueX0.lean`, about `M(s)` alone) asks: for the top `t` of the last
column `x₀` with root `r = left(t)` in the column `c_r`, a node `o = (x, C)` with
`c_r < x < x₀`, `C` a limit row (zero finite coefficient, not the bottom row) below `τ = row t`,
a node `o⁺` above `o` below `τ`, the leg `l > c_r` of `o`, `pa = (l, C)` (the highest node of
`l` at or below `C`, at the row `C`) whose in-row parents reach the column `c_r`, and the node
`g = (c_r, C)` with a node `g⁺` above it below `τ`: `v(g) < v(o)`.

It fails for `s = (1,4,18,56,18)`. The mountain, with Lean indices (index `0` is the phantom;
the JS index of `reference/official/omegay.cjs` is the Lean index minus one), official rows,
values and left ends:

```
column 0: [1] 0:1
column 1: [1] 0:4   [2] 1:3 ←(0,1)  [3] ω:2 ←(0,1)  [4] ω²:1 ←(0,1)
column 2: [1] 0:18  [2] 1:14 ←(1,1) [3] 2:11 ←(1,2) [4] ω:8 ←(1,2)  [5] ω+1:6 ←(1,3)
          [6] ω·2:4 ←(1,3)  [7] ω²:2 ←(1,3)  [8] ω²+1:1 ←(1,4)
column 3: [1] 0:56  [2] 1:38 ←(2,1) [3] 2:24 ←(2,2) [4] 3:13 ←(2,3) [5] ω:2 ←(2,3)
          [6] ω²:1 ←(0,1)
column 4: the same as column 2 (its top [8] has row ω²+1 and left end (1,4))
```

* `t = (4,8)`, `τ = ω² + 1`, root `r = (1,4)` (row `ω²`), `c_r = 1`, `x₀ = 4`;
* `o = (3,5)`: row `C = ω`, value `2`, left end `(2,3)` (leg `l = 2 > c_r`); `o⁺ = (3,6)` has row
  `ω² < τ`;
* `pa = (2,4)`: row `ω`; its in-row parent is `(1,3)` (the left end of `(2,5)`, at the row `ω`),
  in the column `c_r`, so the ascension test of `l` passes;
* `g = (1,3)`: row `ω`, value `2`; `g⁺ = (1,4)` has row `ω² < τ`.

So `v(g) = 2 = v(o)`: the inequality fails. The search for `P(o)` starts at `pa` (value `8`),
rejects `pa` and `g` (values `≥ 2`) and stops at `(0,1)` (value `1`), so `o⁺` has the row
`B(ω, 0) = ω²` and the test from `x = 3` fails (`AscUp` fails too).

The facts about the mountain are the Boolean `cexCheckB`, checked by `#guard` (compiled
evaluation, as `tslrCheck` in `TopStartLoRightFalse.lean`; kernel evaluation of `Canonical.build`
with the rows `ω`, `ω²` runs out of memory). The theorems `not_..._of_check` are proved from
`cexCheckB = true` (no `sorry`, no `native_decide`).

Numerically (`reference/official/tsq-open.cjs --copies 1,2 FILE` with `FILE = [[1,4,18,56,18]]`):
`RootValue FAIL`, `AscUp FAIL`, and also `part TopStartPaOUp FAIL` at `(1,4,18,56,18)[1]`,
`X = 6`, `u = (6,5)` (JS indices); `top-start-fix.cjs` reports `TopStartUp [o<tau, l>cr, plain]
FAIL` there, i.e. the strong clause of `TopStart'` (`HasAboveLow → Stand pe pa`). The target
statements (`recon-targets.cjs`: `ChainHolds`, `CrossChain`, `RowLaw`, `ParentBelow`, ...;
`keylerest-regions.cjs`: `KeyLeShift`) hold on this input. Among the inputs `(1,a,b,c,d)` with
`2 ≤ a` and entries `≤ 64` (searched in order of the largest entry), the first failure is
`(1,4,18,56,18)`; the legal inputs of length `≤ 7` with entries `≤ 12` have no instance of the
hypotheses at all, which is why the earlier small runs saw none.
-/

namespace OmegaY.Official.Recon.TSQ.RVFalse

open Canonical Expansion Classification Reserve Official

/-- The counterexample input. -/
def cexInput : List Nat := [1, 4, 18, 56, 18]

/-- `r = .ok true` as a Boolean. -/
def okTrue : Result Bool → Bool
  | .ok true => true
  | _ => false

/-- `r = .ok false` as a Boolean. -/
def okFalse : Result Bool → Bool
  | .ok false => true
  | _ => false

theorem okTrue_eq {r : Result Bool} (h : okTrue r = true) : r = .ok true := by
  unfold okTrue at h
  split at h
  · rfl
  · cases h

theorem okFalse_eq {r : Result Bool} (h : okFalse r = true) : r = .ok false := by
  unfold okFalse at h
  split at h
  · rfl
  · cases h

/-- The facts about `M(1,4,18,56,18)` used below. -/
def cexCheck (M : Mountain) : Bool :=
  M.size == 5 &&
  okTrue (reachesRoot M 1 (2 + 1) ⟨2, 4⟩) &&
  okFalse (reachesRoot M 1 (3 + 1) ⟨3, 5⟩) &&
  match (M[M.size - 1]?).bind Array.back?, cell? M ⟨3, 5⟩, cell? M ⟨3, 6⟩, cell? M ⟨2, 4⟩,
      cell? M ⟨1, 3⟩, cell? M ⟨1, 4⟩ with
  | some t, some co, some c', some cpa, some cg, some ca =>
      decide (official t.row ≠ 0) && decide (t.left = some ⟨1, 4⟩) &&
      decide (co.row < t.row) && decide (co.left = some ⟨2, 3⟩) &&
      decide (c'.row < t.row) &&
      decide (referenceRow (official co.row) = official co.row) &&
      decide (highestAtMost M 2 co.row = some ⟨2, 4⟩) &&
      decide (cpa.row = co.row) && decide (cg.row = co.row) && decide (co.row ≠ 1) &&
      decide (ca.row < t.row) && decide (cg.value = 2) && decide (co.value = 2) &&
      decide (nodeAt M 2 (referenceRow (official co.row)) = some (⟨2, 4⟩, cpa)) &&
      decide (nodeAt M 3 (referenceRow (official co.row)) = some (⟨3, 5⟩, co))
  | _, _, _, _, _, _ => false

/-- The check on the built mountain (`false` if the build fails). -/
def cexCheckB : Bool :=
  match Canonical.build cexInput with
  | .ok M => cexCheck M
  | .error _ => false

-- Compiled evaluation, not a kernel proof (kernel evaluation of `Canonical.build` on this input
-- runs out of memory: the rows `ω`, `ω²` are `Finsupp`s).
#guard cexCheckB

/-- The unpacked facts of the counterexample. -/
theorem cex_facts (hc0 : cexCheckB = true) : ∃ M t co c' cpa cg ca,
    Recon.Top cexInput M t ⟨1, 4⟩ ∧ M.size = 5 ∧
    cell? M ⟨3, 5⟩ = some co ∧ cell? M ⟨3, 6⟩ = some c' ∧ cell? M ⟨2, 4⟩ = some cpa ∧
    cell? M ⟨1, 3⟩ = some cg ∧ cell? M ⟨1, 4⟩ = some ca ∧
    co.row < t.row ∧ co.left = some ⟨2, 3⟩ ∧ c'.row < t.row ∧
    referenceRow (official co.row) = official co.row ∧
    highestAtMost M 2 co.row = some ⟨2, 4⟩ ∧ cpa.row = co.row ∧
    reachesRoot M 1 (2 + 1) ⟨2, 4⟩ = .ok true ∧
    reachesRoot M 1 (3 + 1) ⟨3, 5⟩ = .ok false ∧
    cg.row = co.row ∧ co.row ≠ 1 ∧ ca.row < t.row ∧ cg.value = 2 ∧ co.value = 2 ∧
    nodeAt M 2 (referenceRow (official co.row)) = some (⟨2, 4⟩, cpa) ∧
    nodeAt M 3 (referenceRow (official co.row)) = some (⟨3, 5⟩, co) := by
  unfold cexCheckB at hc0
  split at hc0
  · rename_i M hb
    have hc : cexCheck M = true := hc0
    simp only [cexCheck, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨hsize, hr1⟩, hr2⟩, hc⟩ := hc
    split at hc
    · rename_i t co c' cpa cg ca ht hco hc' hcpa hcg hca
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hreal, htl⟩, hlt⟩, hol⟩, hc'lt⟩, hZ⟩, hpa⟩, hpar⟩, hgr⟩, hC⟩,
        hcat⟩, hgv⟩, hov⟩, hn2⟩, hn3⟩ := hc
      have hTop : Recon.Top cexInput M t ⟨1, 4⟩ :=
        ⟨hb, ht, hreal, htl, by rw [hsize]; decide⟩
      exact ⟨M, t, co, c', cpa, cg, ca, hTop, hsize, hco, hc', hcpa, hcg, hca, hlt, hol,
        hc'lt, hZ, hpa, hpar, okTrue_eq hr1, okFalse_eq hr2, hgr, hC, hcat, hgv, hov, hn2, hn3⟩
    · cases hc
  · cases hc0

/-- **`RootValueIn` fails if `cexCheckB` holds** (it does, by the `#guard` above; counterexample
`s = (1,4,18,56,18)`, `o = (3,5)`). -/
theorem not_rootValueIn_of_check (hc : cexCheckB = true) : ¬ RVP.RootValueIn := by
  intro h
  obtain ⟨M, t, co, c', cpa, cg, ca, hTop, hsize, hco, hc', hcpa, hcg, hca, hlt, hol, hc'lt, hZ,
    hpa, hpar, hr1, _, hgr, hC, hcat, hgv, hov, _, _⟩ := cex_facts hc
  have := h cexInput M t ⟨1, 4⟩ hTop 3 5 co ⟨2, 3⟩ (by decide) (by rw [hsize]; decide)
    (by decide) hco hlt hol (by decide) ⟨c', hc', hc'lt⟩ hZ ⟨2, 4⟩ cpa hpa hcpa hpar hr1
    ⟨1, 3⟩ cg rfl hcg hgr hC ⟨ca, hca, hcat⟩
  rw [hgv, hov] at this
  exact absurd this (by decide)

/-- `RootValueHi` (`x ≤ x₀`) implies `RootValueIn` (`x < x₀`). -/
theorem rootValueIn_of_hi (h : RVP.RootValueHi) : RVP.RootValueIn := by
  intro s M t root hTop x k co l hcx hxx hk hco hlo hl hlr hab hZ pa cpa hpa hcpa hparow hr' g cg
    hgc hcg hgrow hC hgup
  exact h s M t root hTop x k co l hcx (Nat.le_of_lt hxx) hk hco hlo hl hlr hab hZ pa cpa hpa hcpa
    hparow hr' g cg hgc hcg hgrow hC hgup

/-- `RootValue` implies `RootValueHi`. -/
theorem rootValueHi_of_rootValue (h : RootValue) : RVP.RootValueHi := by
  intro s M t root hTop x k co l hcx hxx hk hco hlo hl hlr hab hZ pa cpa hpa hcpa hparow hr' g cg
    hgc hcg hgrow _ _
  exact h s M t root hTop x k co l hcx hxx hk hco hlo hl hlr hab hZ pa cpa hpa hcpa hparow hr' g
    cg hgc hcg hgrow

/-- **`RootValueHi` fails if `cexCheckB` holds.** -/
theorem not_rootValueHi_of_check (hc : cexCheckB = true) : ¬ RVP.RootValueHi :=
  fun h => not_rootValueIn_of_check hc (rootValueIn_of_hi h)

/-- **`RootValue` fails if `cexCheckB` holds.** -/
theorem not_rootValue_of_check (hc : cexCheckB = true) : ¬ RootValue :=
  fun h => not_rootValueHi_of_check hc (rootValueHi_of_rootValue h)

/-- **`AscUp` fails if `cexCheckB` holds** (same input: the leg column `2` passes the ascension
test of `ω`, the column `3` does not). -/
theorem not_ascUp_of_check (hc : cexCheckB = true) : ¬ AscUp := by
  intro h
  obtain ⟨M, t, co, c', cpa, cg, ca, hTop, hsize, hco, hc', hcpa, hcg, _, hlt, hol, hc'lt, _,
    hpa, hpar, hr1, hr2, hgr, _, _, _, _, hn2, hn3⟩ := cex_facts hc
  obtain ⟨ref, cl, hn, hr⟩ := h cexInput M t ⟨1, 4⟩ hTop 3 5 co ⟨2, 3⟩ (by decide)
    (by rw [hsize]; decide) (by decide) hco hlt hol (by decide) ⟨⟨2, 4⟩, cpa, hpa, hcpa, hpar⟩
    ⟨c', hc', hc'lt⟩ ⟨⟨1, 3⟩, cg, rfl, by decide, hcg, hgr⟩ ⟨2, 4⟩ cpa hn2 hr1
  rw [hn3] at hn
  obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hn)
  rw [hr2] at hr
  cases hr

end OmegaY.Official.Recon.TSQ.RVFalse

#print axioms OmegaY.Official.Recon.TSQ.RVFalse.not_rootValueIn_of_check
#print axioms OmegaY.Official.Recon.TSQ.RVFalse.not_rootValueHi_of_check
#print axioms OmegaY.Official.Recon.TSQ.RVFalse.not_rootValue_of_check
#print axioms OmegaY.Official.Recon.TSQ.RVFalse.not_ascUp_of_check
