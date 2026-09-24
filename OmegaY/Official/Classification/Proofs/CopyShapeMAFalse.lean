import OmegaY.Official.Classification.Proofs.CopyShapeMD

/-!
# (MA) is false, and so is `CopyOrder`

`MAHolds` (`CopyShape.lean`, fact `FactMA` of `CopyShapeItems.lean`) says: in a copied column
`x` of a block `i ≥ 1`, if `x` does not ascend in a reached region `S` whose root-column top
is `ρ`, then no node of `x` in `S` is above `row ρ`.

It fails for `s = (1,3,6,13,15,13)`, `n = 1`. The mountain `M(s)`, in official rows, with the
left end of each node:

```
column 0: 0
column 1: 0 ← (0,·),  1 ← (0,0),  ω ← (0,0)
column 2: 0 ← (1,·),  1 ← (1,0),  2 ← (1,1)
column 3: 0 ← (2,·),  1 ← (2,0),  2 ← (2,1),  3 ← (2,2),  ω ← (2,2),  ω² ← (2,2)
column 4: 0 ← (3,·),  1 ← (3,0),  ω ← (0,0)
column 5: 0 ← (4,·),  1 ← (2,0),  2 ← (2,1),  3 ← (2,2),  ω ← (2,2),  ω² ← (2,2)
```

The top `t` of column `5` has row `τ = ω²` and root `(2,2)`, so `c_r = 2`, `w = 3`. The first
item of the lower part is the region `S = [0, ω²)` of level `3` (`d = 1`). The top of the root
column in `S` is `ρ = (2,2)`, of row `2`; its reference row is `1`. The node `(4,1)` of column
`x = 4` has no in-row parent (the node above it, `(4,ω)`, has its left end `(0,0)` on row `0`),
so `x` does not ascend in `S`. But `(4,ω)` is a node of `x` in `S` above row `2`.

The same input breaks `ChainCorr.CopyOrder` (`ChainCorrStartCopy.lean`): in block `1`, the
node `(3,ω)` of column `3` is copied (plain origin) to row `ω·2`, the node `(4,ω)` of column `4`
(plain origin, same row `ω`) to row `ω`. So the copies of two nodes of the same row get
different rows. `CopyOrder` was derived from MA, MD, MH (`copyOrder_of_MA_MH`); that
derivation is sound, and MA is its false premise.

The output is `s[1] = (1,3,6,13,15,12,29,31)`; the run is a splice run (`SpliceData`, with
the reconstruction `Canonical.build out = R` checked for this input).

What is proved, and how:

* `not_maSourceTop` (no hypothesis): the `M(s)` form `MASourceTop` of (MA), for the first
  items of the lower part, is false. The facts about `M(s)` are checked by `decide +kernel`
  (kernel evaluation of `Canonical.build`, `lowerItems`, `topIn`, `ascends`; no
  `native_decide`).
* `not_maHolds_of_check`, `not_copyOrder_of_check`: `MAHolds` and `ChainCorr.CopyOrder` are
  false, given `cexCheck = true`. `cexCheck` evaluates the run (`Official.expandDiagram`,
  `Official.expand`, the reconstruction, `ChainCorr.blockEmits`); it holds by `#guard`
  (compiled evaluation, not a kernel proof), because the run does not reduce in the kernel
  (see the section before `cexCheck`).
* `not_maHolds_of_splice`: `MAHolds` is false as soon as the run of `s` with `n = 1` is a
  splice run (`∃ M out ρ R t, SpliceData …`); all facts about `M(s)` it uses come from the
  kernel-checked `ma_check`, so this existence is its only assumption.

## Numerical evidence (`reference/official/copy-shape.cjs` and a search over `M(s)` alone)

* legal inputs of length `≤ 6` with entries `≤ 12` (248831 inputs): the `M(s)`-form of MA
  (every region below `τ` with a root top, every column `c_r < x ≤ x₀`) holds (534850 cases);
* the 64 inputs on which `LegBelowTop` fails: MA holds (138 run cases, 24 `M(s)` cases);
* legal inputs of length `≤ 6` with entries `≤ 26`: MA fails on 660 of them; the smallest
  largest entry is `15`, first `(1,3,6,13,15,13)`;
* legal inputs of length `≤ 7` with entries `≤ 14`: MA fails on one, `(1,2,4,10,11,14,10)`;
* inputs `(1,3,a,b,c,d)` with `a,b,c ≤ 40`, `2 ≤ d ≤ 40`: MA fails on 8095 of them;
* random legal inputs (200000, length `≤ 8`, entries `≤ 40`): 27 fail.

On the 60 legal inputs of length `≤ 6` with entries `≤ 20` on which MA fails (`n = 1, 2`):
the run form of MA fails 360 times and `CopyOrder` 868 times, while `CopyEmitted`,
`CopyFirst` and MH hold (MH 520 times, always even `h_ρ ≤ h_q`), `KeyLeShift`
(`keylerest-regions.cjs`, 6889 nodes) and the classification (`reserve.cjs --cand legOnly,leg
--top-control`) hold. `chain-corr.cjs` reports failures of `StartCopy` (30), `StartLeg` (123) and
`StepInner (m' > cr)` (123) on these inputs (e.g. `(1,3,10,12,18,10)[1]`), so `StartCopy` and
`StepInner` are numerically false too.

In every failure seen the reason is the same: the column `x` has a node at the reference row
of `ρ` whose in-row parent is missing (the edge above it has its left end on a lower row), and
the column continues inside `S` above `ρ` through that edge.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.MAFalse

open Canonical Reserve Official Descent Classification Proofs

/-- The counterexample input. -/
def cexInput : List Nat := [1, 3, 6, 13, 15, 13]

/-- The degree bound used for `root?` and `DegreeOK`. -/
def cexD : Nat := 40

/-! ## The `M(s)` form of (MA), refuted in the kernel -/

/-- (MA) as a statement about `M(s)` alone, for the first items of the lower part: for the
top `t` of the last column with root `root`, a first item `L` (level `d + 2`) of the lower part,
the top `ρ` of the root column in `L`, and a column `x > c_r` that does not ascend in `L`
(`Official.ascends`, which reads only the source, `x` and `c_r` of the context), every node of
`x` in `L` has row at most `row ρ`. -/
def MASourceTop : Prop :=
  ∀ (s : List Nat) (M : Mountain), Canonical.build s = .ok M →
    ∀ (col : Column) (t : Cell), M[M.size - 1]? = some col → col.back? = some t →
    ∀ root : Ref, t.left = some root →
    ∀ (d : Nat) (it : Item), (d + 2, it) ∈ lowerItems (official t.row) →
    ∀ ρr ρc, topIn M root.column (d + 2) it.source = some (ρr, ρc) →
    ∀ x, root.column < x → x < M.size →
    ∀ (R : Mountain) (i w x0 : Nat), ascends ⟨M, R, x, i, root.column, w, x0⟩ (some (ρr, ρc)) = .ok false →
    ∀ (q : Ref) (c : Cell), q.column = x → 1 ≤ q.index → cell? M q = some c →
      inRegion (d + 2) it.source (official c.row) = true → official c.row ≤ official ρc.row

/-- `ascends` reads only the source, the column and the root column of the context. -/
theorem ascends_congr {ctx ctx' : Context} (hs : ctx.source = ctx'.source) (hx : ctx.x = ctx'.x)
    (hr : ctx.rootColumn = ctx'.rootColumn) (rho : Option (Ref × Cell)) :
    ascends ctx rho = ascends ctx' rho := by
  cases ctx
  cases ctx'
  simp only at hs hx hr
  subst hs hx hr
  rfl

/-- The facts about `M(1,3,6,13,15,13)` alone. -/
def maCheck (M : Mountain) : Bool :=
  M.size == 6 &&
  match (M[M.size - 1]?).bind Array.back? with
  | some t =>
      decide (t.left = some ⟨2, 3⟩) &&
      (match lowerItems (official t.row) with
        | (lvl, it) :: _ =>
            lvl == 3 &&
            (match topIn M 2 3 it.source with
              | some (ρr, ρc) =>
                  (match ascends ⟨M, #[], 4, 1, 2, 3, 5⟩ (some (ρr, ρc)) with
                    | .ok b => !b
                    | .error _ => false) &&
                  (match cell? M ⟨4, 3⟩ with
                    | some c => inRegion 3 it.source (official c.row) &&
                        decide (¬ official c.row ≤ official ρc.row)
                    | none => false)
              | none => false)
        | [] => false)
  | none => false

/-- Kernel evaluation of `Canonical.build` and of the queries of `maCheck`. -/
theorem ma_check : (Canonical.build cexInput).map maCheck = .ok true := by
  decide +kernel

/-- **The `M(s)` form of (MA) is false** (kernel-checked, counterexample
`s = (1,3,6,13,15,13)`, column `4`, first item `[0, ω²)`). -/
theorem not_maSourceTop : ¬ MASourceTop := by
  intro h
  have hc0 := ma_check
  cases hb : Canonical.build cexInput with
  | error e => rw [hb] at hc0; cases hc0
  | ok M =>
      rw [hb] at hc0
      have hc : maCheck M = true := by simpa only [Except.map, Except.ok.injEq] using hc0
      unfold maCheck at hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨hsize, hc⟩ := hc
      split at hc
      · rename_i t ht
        obtain ⟨col, hcol, htb⟩ := Option.bind_eq_some_iff.mp ht
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨htl, hc⟩ := hc
        split at hc
        · rename_i lvl it tail hl
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨hlvl, hc⟩ := hc
          subst hlvl
          split at hc
          · rename_i ρr ρc hρt
            simp only [Bool.and_eq_true] at hc
            obtain ⟨hasc, hcell⟩ := hc
            have hasc' : ascends ⟨M, #[], 4, 1, 2, 3, 5⟩ (some (ρr, ρc)) = .ok false := by
              split at hasc
              · rename_i b hb'
                simp only [Bool.not_eq_true'] at hasc
                rw [hb', hasc]
              · cases hasc
            split at hcell
            · rename_i c hcq
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
              have hmem : (1 + 2, it) ∈ lowerItems (official t.row) := by
                rw [hl]; exact List.mem_cons_self
              exact hcell.2 (h cexInput M hb col t hcol htb ⟨2, 3⟩ htl 1 it hmem ρr ρc hρt 4
                (by decide) (by rw [hsize]; decide) #[] 1 3 5 hasc' ⟨4, 3⟩ c rfl (by decide) hcq
                hcell.1)
            · cases hcell
          · cases hc
        · cases hc
      · cases hc

/-! ## (MA) and `CopyOrder` for the run, from a compiled check

The run itself (`Official.expandDiagram`, `Official.expand`, the reconstruction
`Canonical.build out = R`, the traced rule `ChainCorr.blockEmits`) does not reduce in the
kernel: the derived `DecidableEq Row` compares two `Row`s through an `Eq.rec` on the equality
of their `Finsupp` fields, which gets stuck when the two rows are built differently (for
example `Row.bump 0 1` and `Row.ofList [0, 1]`; `decide` reports the stuck `⋯ ▸ isTrue ⋯`), and
`nodeAt` compares rows of `M(s)` with rows made by `slot`. So the facts about the run are a
Boolean `cexCheck`, evaluated by `#guard` (compiled code, not a kernel proof), and the two
theorems below take `cexCheck = true` as a hypothesis. They use no axiom beyond the standard
ones. -/

/-- The facts about the run of `cexInput` with `n = 1` (see the module doc). -/
def cexCheck : Bool :=
  match Canonical.build cexInput, Official.expandDiagram cexInput 1, Official.expand cexInput 1 with
  | .ok M, .ok R, .ok out =>
    (match Canonical.build out with
      | .ok R' => decide (R' = R)
      | .error _ => false) &&
    degreeAtMost M cexD &&
    (match root? M cexD with
      | some ρ => ρ.cr == 2 && ρ.x0 == 5
      | none => false) &&
    (match (M[M.size - 1]?).bind Array.back? with
      | some t =>
        (match lowerItems (official t.row) with
          | (lvl, it) :: _ =>
              lvl == 3 &&
              (match topIn M 2 3 it.source with
                | some (ρr, ρc) =>
                    (match ascends (ctxAt M R 4 1 2 (5 - 2) 5 (4 + (5 - 2) * 1))
                        (some (ρr, ρc)) with
                      | .ok b => !b
                      | .error _ => false) &&
                    (match cell? M ⟨4, 3⟩ with
                      | some c => inRegion 3 it.source (official c.row) &&
                          decide (¬ official c.row ≤ official ρc.row)
                      | none => false)
                | none => false)
          | [] => false) &&
        (match ChainCorr.blockEmits M R 2 5 (official t.row) 1 3,
            ChainCorr.blockEmits M R 2 5 (official t.row) 1 4 with
          | .ok es, .ok es' =>
              (match es[7]?, es'[2]? with
                | some p, some p' =>
                    !ChainCorr.cutOrigin p.2 && !ChainCorr.cutOrigin p'.2 &&
                    (match cell? M p.2.src, cell? M p'.2.src with
                      | some c, some c' => decide (c.row = c'.row) && decide (p.1.row ≠ p'.1.row)
                      | _, _ => false)
                | _, _ => false)
          | _, _ => false)
      | none => false)
  | _, _, _ => false

-- Compiled evaluation, not a kernel proof (see the module doc): `cexCheck` holds.
#guard cexCheck

/-- The run of `cexInput` is a splice run, with the facts of `cexCheck`. -/
theorem cex_data (hcheck : cexCheck = true) : ∃ M out ρ R t, ChainCorr.SpliceData cexInput 1 cexD M out ρ R t ∧
    ρ.cr = 2 ∧ ρ.x0 = 5 ∧
    (∃ (lvl : Nat) (it : Item) (tail : List (Nat × Item)),
      lowerItems (official t.row) = (lvl, it) :: tail ∧ lvl = 3 ∧
      ∃ ρr ρc, topIn M 2 3 it.source = some (ρr, ρc) ∧
        ascends (ctxAt M R 4 1 2 (5 - 2) 5 (4 + (5 - 2) * 1)) (some (ρr, ρc)) = .ok false ∧
        ∃ c, cell? M ⟨4, 3⟩ = some c ∧ inRegion 3 it.source (official c.row) = true ∧
          ¬ official c.row ≤ official ρc.row) ∧
    (∃ es es', ChainCorr.blockEmits M R 2 5 (official t.row) 1 3 = .ok es ∧
      ChainCorr.blockEmits M R 2 5 (official t.row) 1 4 = .ok es' ∧
      ∃ p p', es[7]? = some p ∧ es'[2]? = some p' ∧
        ChainCorr.cutOrigin p.2 = false ∧ ChainCorr.cutOrigin p'.2 = false ∧
        ∃ c c', cell? M p.2.src = some c ∧ cell? M p'.2.src = some c' ∧
          c.row = c'.row ∧ p.1.row ≠ p'.1.row) := by
  have h := hcheck
  unfold cexCheck at h
  split at h
  · rename_i M R out hb hd hx
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hcanon, hdeg⟩, hroot⟩, hlast⟩ := h
    -- the reconstruction
    have hcanon' : Canonical.build out = .ok R := by
      split at hcanon
      · rename_i R' hR'
        have := of_decide_eq_true hcanon
        rw [hR', this]
      · cases hcanon
    -- the root
    split at hroot
    · rename_i ρ hρ
      simp only [Bool.and_eq_true, beq_iff_eq] at hroot
      obtain ⟨hcr, hx0⟩ := hroot
      split at hlast
      · rename_i t ht
        obtain ⟨col, hcol, htb⟩ := Option.bind_eq_some_iff.mp ht
        simp only [Bool.and_eq_true] at hlast
        obtain ⟨hlow, hemit⟩ := hlast
        have hS : ChainCorr.SpliceData cexInput 1 cexD M out ρ R t :=
          ⟨⟨hb, hx, hρ, by decide⟩, fun M' hM' => by rw [hb] at hM'; cases hM'; exact hdeg, hd,
            hcanon', ⟨col, hcol, htb⟩⟩
        refine ⟨M, out, ρ, R, t, hS, hcr, hx0, ?_, ?_⟩
        · split at hlow
          · rename_i lvl it tail hl
            simp only [Bool.and_eq_true, beq_iff_eq] at hlow
            obtain ⟨hlvl, htop⟩ := hlow
            refine ⟨lvl, it, tail, hl, hlvl, ?_⟩
            split at htop
            · rename_i ρr ρc hρt
              simp only [Bool.and_eq_true] at htop
              obtain ⟨hasc, hcell⟩ := htop
              refine ⟨ρr, ρc, hρt, ?_, ?_⟩
              · split at hasc
                · rename_i b hb'
                  simp only [Bool.not_eq_true'] at hasc
                  rw [hb', hasc]
                · cases hasc
              · split at hcell
                · rename_i c hc
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
                  exact ⟨c, hc, hcell.1, hcell.2⟩
                · cases hcell
            · cases htop
          · cases hlow
        · split at hemit
          · rename_i es es' he he'
            refine ⟨es, es', he, he', ?_⟩
            split at hemit
            · rename_i p p' hp hp'
              simp only [Bool.and_eq_true, Bool.not_eq_true'] at hemit
              obtain ⟨⟨hcp, hcp'⟩, hcells⟩ := hemit
              refine ⟨p, p', hp, hp', hcp, hcp', ?_⟩
              split at hcells
              · rename_i c c' hc hc'
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hcells
                exact ⟨c, c', hc, hc', hcells.1, hcells.2⟩
              · cases hcells
            · cases hemit
          · cases hemit
      · cases hlast
    · cases hroot
  · cases h

/-- **(MA) is false** (counterexample `s = (1,3,6,13,15,13)`, `n = 1`, block `1`, column `4`,
the region `[0, ω²)` of level `3`). -/
theorem not_maHolds_of_check (hcheck : cexCheck = true) : ¬ MAHolds := by
  intro hMA
  obtain ⟨M, out, ρ, R, t, hS, hcr, hx0, ⟨lvl, it, tail, hl, hlvl, ρr, ρc, hρt, hasc, c, hc,
    hreg, hnot⟩, _⟩ := cex_data hcheck
  have hy : (4 : Nat) ∈ blockColumns ρ.cr ρ.x0 1 1 := by rw [hcr, hx0]; decide
  have hfact := hMA cexInput 1 cexD M out ρ R t hS 1 (by decide) (by decide) 4 hy
  rw [hcr, hx0] at hfact
  subst hlvl
  have hmem : (1 + 2, it) ∈ lowerItems (official t.row) := by rw [hl]; exact List.mem_cons_self
  exact hnot (hfact 1 it (Reach.top hmem) ρr ρc hρt hasc ⟨4, 3⟩ c rfl (by decide) hc hreg)

/-- **(MA) is false as soon as the run of `(1,3,6,13,15,13)` with `n = 1` is a splice run.**
Only the existence of the splice data is assumed; every fact about `M(s)` used here is the
kernel-checked `ma_check`. -/
theorem not_maHolds_of_splice
    (hrun : ∃ M out ρ R t, ChainCorr.SpliceData cexInput 1 cexD M out ρ R t) : ¬ MAHolds := by
  intro hMA
  obtain ⟨M, out, ρ, R, t, hS⟩ := hrun
  obtain ⟨col, root, hcol, ht, htl, _, hcr, hx0⟩ := splice_root hS
  have hb := hS.splice.build
  have hc0 := ma_check
  rw [hb] at hc0
  have hc : maCheck M = true := by simpa only [Except.map, Except.ok.injEq] using hc0
  unfold maCheck at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hsize, hc⟩ := hc
  have htt : (M[M.size - 1]?).bind Array.back? = some t := by rw [hcol]; exact ht
  rw [htt] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨htl', hc⟩ := hc
  have hroot : root = ⟨2, 3⟩ := Option.some.inj (htl.symm.trans htl')
  subst hroot
  have hcr2 : ρ.cr = 2 := hcr
  have hx05 : ρ.x0 = 5 := by rw [hx0, hsize]
  split at hc
  · rename_i lvl it tail hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨hlvl, hc⟩ := hc
    subst hlvl
    split at hc
    · rename_i ρr ρc hρt
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hasc, hcell⟩ := hc
      have hasc' : ascends ⟨M, #[], 4, 1, 2, 3, 5⟩ (some (ρr, ρc)) = .ok false := by
        split at hasc
        · rename_i b hb'
          simp only [Bool.not_eq_true'] at hasc
          rw [hb', hasc]
        · cases hasc
      split at hcell
      · rename_i c hcq
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcell
        have hy : (4 : Nat) ∈ blockColumns ρ.cr ρ.x0 1 1 := by rw [hcr2, hx05]; decide
        have hfact := hMA cexInput 1 cexD M out ρ R t hS 1 (by decide) (by decide) 4 hy
        have hmem : (1 + 2, it) ∈ lowerItems (official t.row) := by
          rw [hl]; exact List.mem_cons_self
        refine hcell.2 (hfact 1 it (Reach.top hmem) ρr ρc ?_ ?_ ⟨4, 3⟩ c rfl (by decide) hcq
          hcell.1)
        · show topIn M ρ.cr (1 + 2) it.source = some (ρr, ρc)
          rw [hcr2]; exact hρt
        · exact (ascends_congr
            (ctx := ctxAt M R 4 1 ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (4 + (ρ.x0 - ρ.cr) * 1))
            (ctx' := ⟨M, #[], 4, 1, 2, 3, 5⟩) rfl rfl hcr2 _).trans hasc'
      · cases hcell
    · cases hc
  · cases hc

/-- **`CopyOrder` is false** (same run: the plain copies of `(3,ω)` and `(4,ω)` in block `1`
get the rows `ω·2` and `ω`). -/
theorem not_copyOrder_of_check (hcheck : cexCheck = true) : ¬ ChainCorr.CopyOrder := by
  intro hCO
  obtain ⟨M, out, ρ, R, t, hS, hcr, hx0, _, es, es', he, he', p, p', hp, hp', hcp, hcp', c, c',
    hc, hc', hrow, hne⟩ := cex_data hcheck
  obtain ⟨hk, rfl⟩ := List.getElem?_eq_some_iff.mp hp
  obtain ⟨hk', rfl⟩ := List.getElem?_eq_some_iff.mp hp'
  have h3 : (3 : Nat) ∈ blockColumns ρ.cr ρ.x0 1 1 := by rw [hcr, hx0]; decide
  have h4 : (4 : Nat) ∈ blockColumns ρ.cr ρ.x0 1 1 := by rw [hcr, hx0]; decide
  have := hCO cexInput 1 cexD M out ρ R t hS 1 (by decide) (by decide) 3 4 es es' h3 h4
    (by rw [hcr, hx0]; exact he) (by rw [hcr, hx0]; exact he') 7 hk 2 hk' hcp hcp' c c' hc hc'
  exact hne (this.2 hrow)

/-- MA fails, so `copyOrder_of_MA_MH` cannot be used; its conclusion is false as well. -/
theorem not_MA_and_copyOrder_of_check (hcheck : cexCheck = true) :
    ¬ MAHolds ∧ ¬ ChainCorr.CopyOrder :=
  ⟨not_maHolds_of_check hcheck, not_copyOrder_of_check hcheck⟩

end OmegaY.Official.Classification.Proofs.CopyShape.MAFalse

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.MAFalse.not_maSourceTop
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.MAFalse.not_maHolds_of_check
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.MAFalse.not_maHolds_of_splice
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.MAFalse.not_copyOrder_of_check
