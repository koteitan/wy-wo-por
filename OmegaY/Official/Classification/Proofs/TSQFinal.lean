import OmegaY.Official.Classification.Proofs.TSQMain
import OmegaY.Official.Classification.Proofs.TSQRootValueParts
import OmegaY.Official.Classification.Proofs.TSQBiTopMain
import OmegaY.Official.Classification.Proofs.TSQCutGapMain
import OmegaY.Official.Classification.Proofs.TSQRootValueX0

set_option autoImplicit false

/-!
# `TopStart'` from `CutParentNT` and `RootValueIn` (`TSQ`)

The four parts of `TopStart'` (`TopStartFixParts.topStart'_of_parts4`):

| part | status | file |
|---|---|---|
| `TopStartLoRootW` | from `CutParentNT` (stage-D statement, another package) | `TSQRoot.lean` |
| `StartRootTopUp` | **proved** (`BiTopLow` proved) | `TSQBiTop*.lean`, `TSQRootTop.lean` |
| `TopStartPaOUp` | from `RootValueIn` (open, about `M(s)` alone) | `TSQRootValue*.lean`, `TSQAscUp.lean`, `TSQPaO.lean` |
| `TopStartCutRight` | **proved** (`CutTopGap` proved) | `TSQCutGap*.lean`, `TSQCutRight.lean` |

`RootValueIn` is `RootValue` in its one remaining case: the row `C` of `o` is not the bottom row
(its finite coefficient is `0`), the root column has a node `g⁺` above `g = (c_r, C)` below `τ`,
and `o` is strictly left of the last column `x₀`. The other cases of `RootValue` are proved
(`RVP.rootValue_of_hi`, `RVP.rootValueHi_of_in`).

* `topStart'_of_cutParent_rootValueHi : CutParentNT → RootValueHi → TopStart'`;
* `topStart'_of_cutParent_rootValueIn : CutParentNT → RootValueIn → TopStart'`.
-/

namespace OmegaY.Official.Recon.TSQ

/-- **`TopStartCutRight` holds.** -/
theorem topStartCutRight : TopStartFixParts.TopStartCutRight :=
  topStartCutRight_of_gap CTG.cutTopGap

/-- **`TopStart'` from `CutParentNT` and `RootValueHi`.** -/
theorem topStart'_of_cutParent_rootValueHi (hCP : Recon.TopChain.Seam.CutParentNT)
    (hRV : RVP.RootValueHi) : Classification.Proofs.ChainCorr.TopStartFix.TopStart' :=
  TopStartFixParts.topStart'_of_parts4 (topStartLoRootW_of_cutParent hCP) BTL.startRootTopUp
    (RVP.topStartPaOUp_of_rootValueHi hRV) topStartCutRight

/-- **`TopStart'` from `CutParentNT` and `RootValueIn`.** -/
theorem topStart'_of_cutParent_rootValueIn (hCP : Recon.TopChain.Seam.CutParentNT)
    (hRV : RVP.RootValueIn) : Classification.Proofs.ChainCorr.TopStartFix.TopStart' :=
  topStart'_of_cutParent_rootValueHi hCP (RVP.rootValueHi_of_in hRV)

end OmegaY.Official.Recon.TSQ

#print axioms OmegaY.Official.Recon.TSQ.BTL.biTopLow
#print axioms OmegaY.Official.Recon.TSQ.BTL.startRootTopUp
#print axioms OmegaY.Official.Recon.TSQ.CTG.cutTopGap
#print axioms OmegaY.Official.Recon.TSQ.topStartCutRight
#print axioms OmegaY.Official.Recon.TSQ.RVP.rootValue_of_hi
#print axioms OmegaY.Official.Recon.TSQ.topStart'_of_cutParent_rootValueHi
#print axioms OmegaY.Official.Recon.TSQ.RVP.rootValueHi_of_in
#print axioms OmegaY.Official.Recon.TSQ.topStart'_of_cutParent_rootValueIn
