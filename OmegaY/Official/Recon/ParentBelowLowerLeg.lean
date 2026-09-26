import OmegaY.Official.Recon.ParentBelowLowerMain
import OmegaY.Official.Classification.Proofs.ChainCorrStartLegJump

/-!
# `LegRight` from `LegBelowTop`

The profile statement `LegRight` (in the copy of a column `y > c_r`, every emitted leg of the
lower part is at least `c_r`) follows from the statement `LegBelowTop` about `M(s)` alone
(`ChainCorrStartLegJump.lean`): the leg of a lower copy is the leg of its origin, a node of
`y` below `τ`. So `LowerParentBelowHolds` needs the seven other parts of the profile and
`LegBelowTop` (`lowerParentBelowHolds_of_parts`).

**Warning.** `LegBelowTop` is false (`LegBelowTopFalse.lean`, `not_legBelowTop`), and so is
`LegRight` (`not_legRight_of_check` below: `legCheck` evaluates the rule on
`(1,2,4,8,10,8)[1]`; it is checked by `#guard`, i.e. compiled evaluation, since
`List.mergeSort` in `Expansion.finish` does not reduce in the kernel). The hypotheses of
`lowerParentBelowHolds_of_parts` and of `lowerParentBelowHolds_of_profile` are therefore
false. `LowerParentBelowHolds` itself holds on that input numerically
(`parent-below-lower.cjs`); what is missing is the case `ℓ < c_r` of `caseLower`.
-/

namespace OmegaY.Official.Recon.LowerPB

open Canonical Expansion Geometry Frame Classification Reserve

/-- **`LegRight` from `LegBelowTop`.** -/
theorem legRight_of_legBelowTop (h : Proofs.ChainCorr.LegJump.LegBelowTop) : LegRight := by
  intro s n R _ M t root hTop i _ _ ctx hB hx es hes e he l hl
  obtain ⟨k, cv, hsrc, hk, hcv, hleft⟩ := lowerT_src hes he
  rw [hB.source] at hcv
  obtain ⟨cb, hcb, hcbτ⟩ := lowerT_below hes e he
  rw [hB.source] at hcb
  rcases hleft with ⟨l', hl', hlc⟩ | ⟨hn, _⟩
  · have hll : l = l'.column := Option.some.inj (hl.symm.trans hlc)
    subst hll
    rw [hsrc] at hcb
    have hcc : cb = cv := Option.some.inj (hcb.symm.trans hcv)
    subst hcc
    have hxle : ctx.x ≤ M.size - 1 := hB.xle
    exact h s M t root hTop ⟨ctx.x, k⟩ cb l' hx hxle hcv hl'
      (row_lt_of_official hTop.row_one_le hcbτ)
  · rw [hn] at hl
    cases hl

/-- The profile without `LegRight`. -/
structure Profile7 : Prop where
  nonCutOrder : NonCutOrder
  cutBetween : CutBetween
  cutOrder : CutOrder
  cutLeg : CutLeg
  emitted : Emitted
  lift : Lift
  boundary : Boundary

/-- **`LowerParentBelowHolds` from seven parts of the profile and `LegBelowTop`.** -/
theorem lowerParentBelowHolds_of_parts (hP : Profile7)
    (hL : Proofs.ChainCorr.LegJump.LegBelowTop) : LowerParentBelowHolds :=
  lowerParentBelowHolds_of_profile ⟨hP.nonCutOrder, hP.cutBetween, hP.cutOrder, hP.cutLeg,
    hP.emitted, hP.lift, legRight_of_legBelowTop hL, hP.boundary⟩

/-- **`ParentBelowHolds` from the same.** -/
theorem parentBelowHolds_of_parts (hP : Profile7)
    (hL : Proofs.ChainCorr.LegJump.LegBelowTop) : ParentBelowHolds :=
  parentBelowHolds_of_lower (lowerParentBelowHolds_of_parts hP hL)

/-! ## `LegRight` is false -/

open Official in
/-- The copy of column `4` in block `1` of `(1,2,4,8,10,8)[1]` has a lower emitted node whose
leg column is `< 2 = c_r`. -/
def legCheck : Bool :=
  match Canonical.build [1, 2, 4, 8, 10, 8], Official.expandDiagram [1, 2, 4, 8, 10, 8] 1 with
  | .ok M, .ok R =>
    match (M[M.size - 1]?).bind Array.back? with
    | some t =>
      M.size == 6 && decide (t.left = some ⟨2, 3⟩) && decide (official t.row ≠ 0) &&
        match lowerT ⟨M, R, 4, 1, 2, M.size - 1 - 2, M.size - 1⟩ (official t.row) with
        | .ok es => es.any (fun e => e.1.leftColumn.any (· < 2))
        | .error _ => false
    | none => false
  | _, _ => false

-- Compiled evaluation, not a kernel proof: `List.mergeSort` in `Expansion.finish` does not
-- reduce in the kernel.
#guard legCheck

open Official in
/-- **`LegRight` fails if `legCheck` holds** (it does, by the `#guard` above). -/
theorem not_legRight_of_check (hc : legCheck = true) : ¬ LegRight := by
  intro h
  unfold legCheck at hc
  split at hc
  · rename_i M R hb hR
    split at hc
    · rename_i t ht
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hsize, htl⟩, hreal⟩, hc⟩ := hc
      split at hc
      · rename_i es hes
        obtain ⟨e, he, hp⟩ := List.any_eq_true.mp hc
        cases hl : e.1.leftColumn with
        | none => rw [hl] at hp; cases hp
        | some l =>
            rw [hl] at hp
            have hl2 : l < 2 := by simpa using hp
            have hTop : Top [1, 2, 4, 8, 10, 8] M t ⟨2, 3⟩ :=
              ⟨hb, ht, hreal, htl, by rw [hsize]; decide⟩
            have hB : BCtx M R (⟨2, 3⟩ : Ref).column (M.size - 1) 1
                ⟨M, R, 4, 1, 2, M.size - 1 - 2, M.size - 1⟩ :=
              ⟨rfl, rfl, rfl, rfl, rfl, (show 2 ≤ 4 by omega), (show 4 ≤ M.size - 1 by omega), rfl⟩
            have := h _ 1 R hR M t ⟨2, 3⟩ hTop 1 (le_refl _) (le_refl _) _ hB
              (show 2 < 4 by omega) es hes e he l hl
            simp at this
            omega
      · cases hc
    · cases hc
  · cases hc

end OmegaY.Official.Recon.LowerPB

#print axioms OmegaY.Official.Recon.LowerPB.legRight_of_legBelowTop
#print axioms OmegaY.Official.Recon.LowerPB.lowerParentBelowHolds_of_parts
#print axioms OmegaY.Official.Recon.LowerPB.parentBelowHolds_of_parts
#print axioms OmegaY.Official.Recon.LowerPB.not_legRight_of_check
