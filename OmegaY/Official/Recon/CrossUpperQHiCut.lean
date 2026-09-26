import OmegaY.Official.Recon.CrossUpperQ
import OmegaY.Official.Classification.Proofs.TSQFinal

set_option autoImplicit false

/-!
# `CutRightTopHi` holds

`CutRightTopHi` (`CrossUpperQ.lean`): the top copy `u` (block `i ≥ 1`) of an origin `o` below `τ`
is a gap copy, the leg `l` of `o` is right of `c_r`, and the node `o⁺` above `o` is at a row
`≥ τ`. Then `pe = hAM_R(φ(l), row u)` is the top copy of `pa = hAM_M(l, row o)` (`TopNode`).

The proved `TSQ.topNode_cutRight` (`TSQCutRight.lean`) gives `TopNode pe pa` from `CutTopGap`
in the setting of `TopStartCutRight` without any hypothesis on the node above `o`, and
`CutTopGap` is proved (`TSQ.CTG.cutTopGap`, `TSQCutGapMain.lean`). The hypothesis
`HasAboveHi` is not used.

Result: `cutRightTopHi : CutRightTopHi`.
-/

namespace OmegaY.Official.Recon.CrossUpperQ.QHi

/-- **`CutRightTopHi` holds.** -/
theorem cutRightTopHi : CutRightTopHi := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo hlr hcut _
  exact OmegaY.Official.Recon.TSQ.topNode_cutRight OmegaY.Official.Recon.TSQ.CTG.cutTopGap hrun
    hTop hi0 hin hx hes hj htop hcu hcv hl hpa hpe hlo hlr hcut

end OmegaY.Official.Recon.CrossUpperQ.QHi

#print axioms OmegaY.Official.Recon.CrossUpperQ.QHi.cutRightTopHi
