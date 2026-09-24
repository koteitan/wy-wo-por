import OmegaY.Official.Classification.Proofs.TopChainMain

set_option autoImplicit false

/-!
# `TopStartLoRight` is false (and so is `TopStart`)

`TopStartLoRight` (`TopChainMain.lean`) asks, for the top copy `u` of an origin `o` below `τ`
whose leg `l` is right of `c_r`, when `u` is a gap copy or `l` has a node at the row of `o`:
`pe = hAM_R(φ(l), row u)` is the top copy of `pa = hAM_M(l, row o)`.

It fails for `s = (1,20,15,23,3,10,28,22)`, `n = 1`, block `i = 1`
(`c_r = 4`, `x₀ = 7`, `w = 3`). Lean indices (index `0` is the phantom; JS index = Lean − 1):

* column `x = 6`, copied to `X = 9`; its emits are
  `[p(6,1), c(6,2), c!(6,2), p(6,3), p(6,4), p(6,5)]`. The last one, `u = (9,6)`, is the top
  copy of the plain origin `o = (6,5)` (row `ω`, below `τ`); the leg of `o` is column `5`;
* `pa = (5,4)`: the highest node of column `5` at or below row `ω`, at the row `ω` of `o`;
* column `5` is copied to `8`, with emits
  `[p(5,1), c(5,2), c!(5,2), p(5,3), c(5,4), c!(5,4), p(5,5), u(5,6)]`;
  `pe = (8,5)` (the clean copy `c(5,4)` of `pa`, row `ω`), but `(8,6)` above it is the gap copy
  `c!(5,4)` of `pa` (row `ω + 1`). So `pe` is not the top copy of `pa`: `Stand pe pa` fails.

Why: `o = (6, ω)` is at the row of the root top `ρ = (4, ω)`; the leg column `5` passes the
ascension test of `row ρ` (so it copies `pa` as root row, clean and then gap copies), while the
column `6` does not (its node `(6, ω)` is the top of column `6`, no in-row parent), so `o` gets
a plain copy at the height of the clean copy of `pa`. This is the case "`row ρ = row v`" where the
converse of `AscLeg.ascLegLe` fails.

`TopStart` (`LowerChain.lean`) has the same conclusion with fewer hypotheses, so it fails on
the same data (`not_topStart_of_check`).

`tslrCheck` evaluates the rule on this input. It is checked by `#guard` (compiled evaluation:
`List.mergeSort` in `Expansion.finish` does not reduce in the kernel), as `bndCheck` in
`Recon/PBStageBBoundaryFalse.lean`. `not_topStartLoRight_of_check` turns the check into a
refutation.

Numerically (`reference/official/top-chain.cjs`, and `lower-chain.cjs` for `TopStart`): the
failure is `TopStartLo [l>cr, plain, pa=o] FAIL` at `(1,20,15,23,3,10,28,22)[1]`, `X = 9`,
`u = (9,5)` (JS indices); it does not occur on the legal inputs of length `≤ 6` with entries `≤ 12`.
The target statements (`KeyLeRest`, the reconstruction statements of `recon-targets.cjs`)
hold on this input.
-/

namespace OmegaY.Official.Recon.TopChain.TSLRFalse

open Canonical Expansion Classification Reserve
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStart IsTopAt)

/-- The counterexample input. -/
def cexInput : List Nat := [1, 20, 15, 23, 3, 10, 28, 22]

open Official in
/-- The data of the counterexample, evaluated by the rule. -/
def tslrCheck : Bool :=
  match Canonical.build cexInput, Official.expandDiagram cexInput 1 with
  | .ok M, .ok R =>
    match (M[M.size - 1]?).bind Array.back? with
    | some t =>
      match t.left with
      | some root =>
        match emitsT (ctxAt M R 6 1 root.column (M.size - 1 - root.column) (M.size - 1)
            (6 + (M.size - 1 - root.column) * 1)) (official t.row) with
        | .ok es =>
          match es[5]?, Reserve.cell? R ⟨6 + (M.size - 1 - root.column) * 1, 5 + 1⟩ with
          | some e, some cu =>
            match Reserve.cell? M e.2.src with
            | some cv =>
              match cv.left with
              | some l =>
                match Reserve.highestAtMost M l.column cv.row,
                    Reserve.highestAtMost R (Reserve.mapColumn root.column
                      ((M.size - 1 - root.column) * 1) l.column) cu.row with
                | some pa, some pe =>
                  match emitsT (ctxAt M R 5 1 root.column (M.size - 1 - root.column)
                      (M.size - 1) pe.column) (official t.row) with
                  | .ok es' =>
                    decide (root.column < M.size - 1) && decide (official t.row ≠ 0) &&
                      decide (es.length = 6) && decide (cv.row < t.row) &&
                      decide (root.column < l.column) &&
                      decide ((Reserve.cell? M pa).map (fun c => c.row) = some cv.row) &&
                      decide (root.column < pa.column) && decide (root.column < 5) &&
                      decide (5 < M.size - 1) &&
                      decide (5 ∈ blockColumns root.column (M.size - 1) 1 1) &&
                      decide (6 ∈ blockColumns root.column (M.size - 1) 1 1) &&
                      decide (pe.column = 5 + (M.size - 1 - root.column) * 1) &&
                      (Reserve.cell? R ⟨pe.column, pe.index + 1⟩).isSome &&
                      decide (es'[pe.index]?.map (fun f => f.2.src) = some pa)
                  | .error _ => false
                | _, _ => false
              | none => false
            | none => false
          | _, _ => false
        | .error _ => false
      | none => false
    | none => false
  | _, _ => false

-- Compiled evaluation, not a kernel proof.
#guard tslrCheck

/-- **`TopStartLoRight` fails if `tslrCheck` holds** (it does, by the `#guard` above). -/
theorem not_topStartLoRight_of_check (hc : tslrCheck = true) : ¬ TopStartLoRight := by
  intro h
  unfold tslrCheck at hc
  split at hc
  · rename_i M R hb hR
    split at hc
    · rename_i t ht
      split at hc
      · rename_i root hl
        split at hc
        · rename_i es hes
          split at hc
          · rename_i e cu he hcu
            split at hc
            · rename_i cv hcv
              split at hc
              · rename_i l hcl
                split at hc
                · rename_i pa pe hpa hpe
                  split at hc
                  · rename_i es' hes'
                    simp only [Bool.and_eq_true, decide_eq_true_eq,
                      Option.isSome_iff_exists] at hc
                    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlt, hreal⟩, hlen⟩, hrow⟩, hlr⟩, hcut⟩, hpac⟩, h5⟩,
                      h5x⟩, hb5⟩, hb6⟩, hpec⟩, ⟨c', hc'⟩⟩, hsrc'⟩ := hc
                    have hTop : Top cexInput M t root := ⟨hb, ht, hreal, hl, hlt⟩
                    have hj : 5 < es.length := by omega
                    have htop : IsTopAt es 5 := by
                      intro j' hj' _ hlt'
                      omega
                    have he5 : es[5] = e := by
                      have := List.getElem?_eq_getElem hj
                      rw [this] at he
                      exact Option.some.inj he
                    have hcv' : Reserve.cell? M es[5].2.src = some cv := by rw [he5]; exact hcv
                    obtain ⟨cp, hcp, hcpr⟩ := Option.map_eq_some_iff.mp hcut
                    have hS := h cexInput 1 R M t root 1 6 hR hTop (by decide) le_rfl hb6 es hes
                      5 hj htop cu cv l pe pa hcu hcv' hcl hpa hpe hrow hlr (Or.inr ⟨cp, hcp, hcpr⟩)
                    have hTN := hS.2.2 hpac
                    -- the gap copy of `pa` above `pe`
                    obtain ⟨f, hf, hfs⟩ := Option.map_eq_some_iff.mp hsrc'
                    obtain ⟨hjf, hf'⟩ := List.getElem?_eq_some_iff.mp hf
                    refine hTN.2.1 ⟨pe.column, pe.index + 1⟩ rfl (by simp) ⟨c', hc'⟩ ?_
                    refine ⟨5, es', pe.index, h5, h5x, hb5, hpec, rfl, hes', hjf, ?_⟩
                    rw [hf']
                    exact hfs
                  · cases hc
                · cases hc
              · cases hc
            · cases hc
          · cases hc
        · cases hc
      · cases hc
    · cases hc
  · cases hc

/-- **`TopStart` fails if `tslrCheck` holds**: `TopStartLoRight` is `TopStart` with more
hypotheses. -/
theorem not_topStart_of_check (hc : tslrCheck = true) : ¬ TopStart := by
  intro h
  apply not_topStartLoRight_of_check hc
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa
    hpe _ _ _
  exact h s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe

end OmegaY.Official.Recon.TopChain.TSLRFalse

#print axioms OmegaY.Official.Recon.TopChain.TSLRFalse.not_topStartLoRight_of_check
#print axioms OmegaY.Official.Recon.TopChain.TSLRFalse.not_topStart_of_check
