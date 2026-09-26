import OmegaY.Official.Classification.Proofs.StartRootPartsOrigin

/-!
# `CutTop` from the profile of a block and `GapTop`

`CutTop` (`ChainCorrStartCopy.lean`): for a node `u` of block `i ≥ 1` that is not a gap copy,
whose origin `o = (x, σ)` has its leg `l` right of `cr`, let `pa` be the highest node of `l` at
or below `σ`. If the copy of `l` in block `i` has a gap copy of `pa` at or below the row of
`u`, then `pa` is the top of its column.

Two cases, by the row of `pa` (at most `σ`):

* **`row pa = σ` (proved).** The first emit of `pa` in the copy of `l` is not a gap copy
  (`CopyFirst`), and by `CopyOrder` it has the row of `u` (equal origin rows give equal rows).
  A gap copy of `pa` comes after it, strictly above the row of `u`: the hypothesis of `CutTop`
  is never met.
* **`row pa < σ` (open, `GapTop`).** If the copy of `l` has any gap copy of `pa`, then `pa` is
  the top of `l`.

`cutTop_of_gapTop`: `CutTop` from `CopyOrder`, `CopyFirst` and `GapTop`.

## Numerical evidence

`reference/official/start-root-parts.cjs` counts, for the nodes of `CutTop`, the pairs where
the copy of `l` has a gap copy of `pa`. On the standard samples S1–S3, S6 (`n = 1, 2, 3`):
59400 of them have `row pa = σ` (all gap copies above `u`), 36 have `row pa < σ` (then `pa` is
always the top of `l`); on 20000 random legal sequences (`--random 20000,10,10,7`): 63249 and
78. No failure of `GapTop`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-- (open) A gap copy of `pa` in the copy of the leg column, with `pa` strictly below the row of
the origin, occurs only when `pa` is the top of its column. -/
def GapTop : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column →
      ∀ esl, blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl →
      ∀ k (hk : k < esl.length), cutOrigin esl[k].2 = true → esl[k].2.src = pa →
        cpa.row < cv.row → rawParent M pa = none

/-- **`CutTop` from the profile of a block and `GapTop`.** -/
theorem cutTop_of_gapTop (hA : CopyOrder) (hC2 : ChainCorr.CopyFirst) (hG : GapTop) :
    CutTop := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt esl hesl k hk
    hcut hsrc hrowle
  by_cases hσ : cpa.row < cv.row
  · exact hG s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt esl hesl k
      hk hcut hsrc hσ
  exfalso
  have heqrow : cpa.row = cv.row := le_antisymm (hAM_le hL.hpa hL.hcpa) (not_lt.mp hσ)
  have hdat := hS.data
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  obtain ⟨_, hcrx, hinv, _⟩ := spliceData_facts hdat
  have hipos := hS.iPos
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  have hblx : blockEmits M R ρ.cr ρ.x0 (official t.row) i x = .ok es := by
    simp only [blockEmits, ← hS.Xeq]
    exact hS.emits
  -- the leg column
  have himg := leg_image hS hj hL
  rw [mapColumn_of_ge (le_of_lt hlt)] at himg
  obtain ⟨hsrcc, _, _, _, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hly : l.column < es[j].2.src.column := left_lt_of_valid hV hL.hcv hL.hl
  have hsrcle : es[j].2.src.column ≤ ρ.x0 := by
    rw [hsrcc]
    split
    · exact upperColumn_le hcrx.le hxx
    · exact hxx
  have hyx : l.column < ρ.x0 := by omega
  have hymem : l.column ∈ blockColumns ρ.cr ρ.x0 n i := by
    unfold blockColumns
    rw [if_neg (by omega)]
    simp only [List.mem_range'_1]
    split <;> omega
  -- the output column of the copy of `l`
  obtain ⟨_, _, colL, hcolL, _, _, _⟩ := highestAtMost_spec hL.hpe
  obtain ⟨hLsz, _⟩ := column_of_getElem? hcolL
  have hL0 : ρ.x0 ≤ ref.column := by
    rw [himg]
    have : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hipos
    omega
  obtain ⟨i', x', _, hx', hLeq, hcopyL⟩ := hinv.2.2 ref.column hLsz hL0
  obtain ⟨hii, hxy⟩ := blockCol_unique_inner hcrx hlt hyx hipos hx' (by rw [← himg]; exact hLeq)
  subst i' x'
  have hcolL' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hLsz
  have hesl' : emitsT (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ref.column)
      (official t.row) = .ok esl := by
    have h' : ref.column = l.column + (ρ.x0 - ρ.cr) * i := himg
    rw [h']
    exact hesl
  obtain ⟨_, hcellsL⟩ := cells_of_copy hcolL' hcopyL hesl'
  have hstrict : ∀ k1 k2 (h1 : k1 < esl.length) (h2 : k2 < esl.length), k1 < k2 →
      esl[k1].1.row < esl[k2].1.row := by
    intro k1 k2 h1 h2 h12
    obtain ⟨c1, hc1, hr1⟩ := hcellsL k1 h1
    obtain ⟨c2, hc2, hr2⟩ := hcellsL k2 h2
    have := cell_row_lt hVR hc1 hc2 (by omega)
    rw [hr1, hr2] at this
    exact stored_lt_iff.mp this
  -- the first emit of `pa`
  obtain ⟨k0, hk0l, hk0src, hk0min⟩ : ∃ k0, ∃ hk0l : k0 < esl.length,
      esl[k0].2.src = pa ∧ ∀ k' (hk' : k' < esl.length), k' < k0 → esl[k'].2.src ≠ pa := by
    classical
    have hex : ∃ k, ∃ hk : k < esl.length, esl[k].2.src = pa := ⟨k, hk, hsrc⟩
    obtain ⟨hk0l, hk0src⟩ := Nat.find_spec hex
    exact ⟨Nat.find hex, hk0l, hk0src, fun k' hk' hlt' heq => Nat.find_min hex hlt' ⟨hk', heq⟩⟩
  have hk0le : k0 ≤ k := by
    by_contra hn
    exact hk0min k hk (by omega) hsrc
  have hk0nc : cutOrigin esl[k0].2 = false := by
    apply hC2 s n D M out ρ R t hdat i hipos hS.iLt l.column esl hlt hyx hesl k0 hk0l
    intro k' hk' hlt' heq
    exact hk0min k' hk' hlt' (heq.trans hk0src)
  have hk0k : k0 < k := by
    rcases Nat.lt_or_eq_of_le hk0le with h' | h'
    · exact h'
    · subst h'
      rw [hcut] at hk0nc
      cases hk0nc
  -- the first emit of `pa` is at the row of `u`
  have hcpa0 : cell? M esl[k0].2.src = some cpa := by rw [hk0src]; exact hL.hcpa
  have hA' := (hA s n D M out ρ R t hdat i hipos hS.iLt l.column x esl es hymem hS.xMem hesl
    hblx k0 hk0l j hj hk0nc hnc cpa cv hcpa0 hL.hcv).2 heqrow
  have := hstrict k0 k hk0l hk hk0k
  rw [hA'] at this
  exact absurd (lt_of_lt_of_le this hrowle) (lt_irrefl _)

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts
