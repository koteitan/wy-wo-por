import OmegaY.Official.Classification.Proofs.SeamCleanStep

set_option autoImplicit false

/-!
# The seam: `TopStepLoRoot`, `TopStartLoRoot`, `BoundaryChain` from three open statements

Proved steps of the chain induction (`SeamChain.lean`): `stepBlock0`, `stepUpper`, `stepTop`,
`stepX0Top` (`SeamX0.lean`), `stepCleanNT` (`SeamCleanStep.lean`). Proved lookups:
`stepRootLookup`, `startRootLookup` (`SeamLookup.lean`); the jump bound `topStepLoJumpAll`
(`SeamReduce.lean`).

Open (numerically checked, `reference/official/seam-open.cjs`):

* `StepCutNT`: the step from a gap copy that is not the top copy of its origin;
* `StepRootTop`: in `TopStepLoRoot`, when the node `a⁺` above `a` is at or above `τ`, the node
  above `A` has the row of `a⁺`;
* `StartRootTop`: in `TopStartLoRoot`, when the node `pa⁺` above `pa` is at or above `τ`, the node
  above `pe` has the row of `pa⁺`.

* `boundaryChain_of_cut : StepCutNT → BoundaryChain`;
* `topStepLoRoot_of_cut : StepCutNT → StepRootTop → TopStepLoRoot`;
* `topStartLoRoot_of_cut : StepCutNT → StartRootTop → TopStartLoRoot`.
-/

namespace OmegaY.Official.Recon.TopChain.Seam

/-- **`BoundaryChainD` from `StepCutNT`.** -/
theorem boundaryChainD_of_cut (hG : StepCutNT) : BoundaryChainD :=
  boundaryChainD_of_open stepX0Top stepCleanNT hG

/-- **`BoundaryChain` from `StepCutNT`.** -/
theorem boundaryChain_of_cut (hG : StepCutNT) : Classification.Proofs.ChainCorr.BoundaryChain :=
  boundaryChain_of_open stepX0Top stepCleanNT hG

/-- **`TopStepLoRoot` from `StepCutNT` and `StepRootTop`.** -/
theorem topStepLoRoot_of_cut (hG : StepCutNT) (hR : StepRootTop) : TopStepLoRoot :=
  topStepLoRoot_of_open stepX0Top stepCleanNT hG hR

/-- **`TopStartLoRoot` from `StepCutNT` and `StartRootTop`.** -/
theorem topStartLoRoot_of_cut (hG : StepCutNT) (hR : StartRootTop) : TopStartLoRoot :=
  topStartLoRoot_of_open stepX0Top stepCleanNT hG hR

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.boundaryChain_of_cut
#print axioms OmegaY.Official.Recon.TopChain.Seam.topStepLoRoot_of_cut
#print axioms OmegaY.Official.Recon.TopChain.Seam.topStartLoRoot_of_cut
