import OmegaY.Official.Recon.CrossUpperQ

set_option autoImplicit false

/-!
# `PaONoGapHi` is false

`PaONoGapHi` (`CrossUpperQ.lean`) asks, for the top copy `u` (not a gap copy) of an origin `o`
below `τ` whose leg `l` is right of `c_r`, with `pa = hAM_M(l, row o)` at the row of `o` and the
node `o⁺` above `o` at a row `≥ τ`: no emit of the copied column `l` whose source is `pa` is a gap
copy.

It fails for `s = (1,21,5,20,59,20)`, `n = 1`, block `i = 1` (`c_r = 2`, `x₀ = 5`, `w = 3`,
`τ = ω·2`, the root `(2, ω)`). Lean indices (index `0` is the phantom; JS index = Lean − 1):

* column `x = 4` (rows `0, 1, 2, 3, ω, ω²`), copied to `X = 7`; its emits are
  `[p(4,1), c(4,2), c!(4,2), p(4,3), p(4,4), p(4,5), u(4,6)]`. The emit `j = 5`, `u = (7,6)`
  (row `ω`), is the top copy of the plain origin `o = (4,5)` (row `ω`); `o⁺ = (4,6)` is at the row
  `ω² ≥ τ`; the leg of `o` is column `3`;
* `pa = (3,4)`: the highest node of column `3` at or below row `ω`, at the row `ω`;
* column `3` is copied to `6`, with emits
  `[p(3,1), c(3,2), c!(3,2), p(3,3), c(3,4), c!(3,4), p(3,5), u(3,6)]`: the emit `j' = 5` is a gap
  copy `c!(3,4)` of `pa`.

Why: the leg column `3` passes the ascension test of `ω` (the in-row parent of `(3,4)` is the
root `(2,3)`), and the root column has its top of the region `ω + ℕ` at `ω`, while `x₀` has
`ω + 1` there, so the tree of `3` emits a clean copy and a gap copy of `pa`. The column `4` does
not pass the test: `P(o) = (0,1)` (the search from `pa` rejects `pa` (value 7) and the root
(value 3), since `v(o) = 2`), so `o⁺ = B(ω, 0) = ω²` and `o` has no in-row parent.

So the reduction `PaONoGap` → `AscUp` → `RootValue` does not extend to `o⁺ ≥ τ`: here
`v(g) = 3 ≥ v(o) = 2` for `g` the root. The same input also refutes the inner clause of the weak
start `CopyQLowerW` numerically: `A = Q_R(U) = (6,5)` is the clean copy of `a = pa`, and the gap
copy `(6,6)` of `a` lies above it, so `A` is not the top copy of `a`
(`cuw7.cjs`: `QInnerTop inner FAIL`, `QInnerPaOHi FAIL`). The target statements of
`recon-targets.cjs` (`RowLaw`, `ChainHolds`, `CrossChain`, `ParentBelow`, ...) and `cross-lex.cjs`
(`CrossLex`) hold on this input (`n = 1, 2`).

`pghCheck` evaluates the rule on this input. It is checked by `#guard` (compiled evaluation,
as `tslrCheck` in `TopStartLoRightFalse.lean`: `List.mergeSort` in `Expansion.finish` does not
reduce in the kernel). `not_paONoGapHi_of_check` turns the check into a refutation.
-/

namespace OmegaY.Official.Recon.CrossUpperQ.QHi

open Canonical Expansion Classification Reserve
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt above)

/-- The counterexample input. -/
def pghInput : List Nat := [1, 21, 5, 20, 59, 20]

open Official in
/-- The data of the counterexample, evaluated by the rule. -/
def pghCheck : Bool :=
  match Canonical.build pghInput, Official.expandDiagram pghInput 1 with
  | .ok M, .ok R =>
    match (M[M.size - 1]?).bind Array.back? with
    | some t =>
      match t.left with
      | some root =>
        match emitsT (ctxAt M R 4 1 root.column (M.size - 1 - root.column) (M.size - 1)
            (4 + (M.size - 1 - root.column) * 1)) (official t.row) with
        | .ok es =>
          match es[5]?, Reserve.cell? R ⟨4 + (M.size - 1 - root.column) * 1, 5 + 1⟩ with
          | some e, some cu =>
            match Reserve.cell? M e.2.src, Reserve.cell? M (above e.2.src) with
            | some cv, some ca =>
              match cv.left with
              | some l =>
                match Reserve.highestAtMost M l.column cv.row,
                    Reserve.highestAtMost R (Reserve.mapColumn root.column
                      ((M.size - 1 - root.column) * 1) l.column) cu.row with
                | some pa, some pe =>
                  match emitsT (ctxAt M R l.column 1 root.column (M.size - 1 - root.column)
                      (M.size - 1) (l.column + (M.size - 1 - root.column) * 1))
                      (official t.row) with
                  | .ok es' =>
                    decide (root.column < M.size - 1) && decide (official t.row ≠ 0) &&
                      decide (es.length = 7) &&
                      decide (es[6]?.map (fun f => f.2.src) ≠ some e.2.src) &&
                      decide (cv.row < t.row) && decide (root.column < l.column) &&
                      (Classification.Proofs.ChainCorr.cutOrigin e.2 == false) &&
                      decide ((Reserve.cell? M pa).map (fun c => c.row) = some cv.row) &&
                      decide (t.row ≤ ca.row) &&
                      decide (4 ∈ blockColumns root.column (M.size - 1) 1 1) &&
                      decide (es'[5]?.map (fun f => f.2.src) = some pa) &&
                      decide (es'[5]?.map (fun f => Classification.Proofs.ChainCorr.cutOrigin f.2)
                        = some true)
                  | .error _ => false
                | _, _ => false
              | none => false
            | _, _ => false
          | _, _ => false
        | .error _ => false
      | none => false
    | none => false
  | _, _ => false

-- Compiled evaluation, not a kernel proof.
#guard pghCheck

/-- **`PaONoGapHi` fails if `pghCheck` holds** (it does, by the `#guard` above). -/
theorem not_paONoGapHi_of_check (hc : pghCheck = true) : ¬ PaONoGapHi := by
  intro h
  unfold pghCheck at hc
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
            · rename_i cv ca hcv hca
              split at hc
              · rename_i l hcl
                split at hc
                · rename_i pa pe hpa hpe
                  split at hc
                  · rename_i es' hes'
                    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
                    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlt, hreal⟩, hlen⟩, h6⟩, hrow⟩, hlr⟩, hcut⟩, hpac⟩, hθ⟩,
                      hb4⟩, hsrc'⟩, hcut'⟩ := hc
                    have hTop : Top pghInput M t root := ⟨hb, ht, hreal, hl, hlt⟩
                    have hj : 5 < es.length := by omega
                    have he5 : es[5] = e := by
                      have := List.getElem?_eq_getElem hj
                      rw [this] at he
                      exact Option.some.inj he
                    have htop : IsTopAt es 5 := by
                      intro j' hj' _ hlt' heq
                      have hj6 : j' = 6 := by omega
                      subst hj6
                      apply h6
                      rw [List.getElem?_eq_getElem hj', Option.map_some, heq, he5]
                    have hcv' : Reserve.cell? M es[5].2.src = some cv := by rw [he5]; exact hcv
                    have hcut5 : Classification.Proofs.ChainCorr.cutOrigin es[5].2 = false := by
                      rw [he5]; exact hcut
                    obtain ⟨cp, hcp, hcpr⟩ := Option.map_eq_some_iff.mp hpac
                    have hHi : HasAboveHi M t.row es[5].2.src := ⟨ca, by rw [he5]; exact hca, hθ⟩
                    have hng := h pghInput 1 R M t root 1 4 hR hTop (by decide) le_rfl hb4 es hes
                      5 hj htop cu cv l pe pa hcu hcv' hcl hpa hpe hrow hlr hcut5
                      ⟨cp, hcp, hcpr⟩ hHi es' hes'
                    obtain ⟨f, hf, hfs⟩ := Option.map_eq_some_iff.mp hsrc'
                    obtain ⟨f', hf', hfc⟩ := Option.map_eq_some_iff.mp hcut'
                    obtain ⟨hjf, hf5⟩ := List.getElem?_eq_some_iff.mp hf
                    have hff : f' = f := Option.some.inj (hf'.symm.trans hf)
                    subst hff
                    have := hng 5 hjf (by rw [hf5]; exact hfs)
                    rw [hf5, hfc] at this
                    cases this
                  · cases hc
                · cases hc
              · cases hc
            · cases hc
          · cases hc
        · cases hc
      · cases hc
    · cases hc
  · cases hc

end OmegaY.Official.Recon.CrossUpperQ.QHi

#print axioms OmegaY.Official.Recon.CrossUpperQ.QHi.not_paONoGapHi_of_check
