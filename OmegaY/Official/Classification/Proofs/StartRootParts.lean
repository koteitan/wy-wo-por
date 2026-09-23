import OmegaY.Official.Classification.Proofs.StartRootPartsBoundary
import OmegaY.Official.Classification.Proofs.StartRootPartsOriginLower
import OmegaY.Official.Classification.Proofs.StartRootPartsCutTop

/-!
# `CutTop`, `BoundaryChain`, `OriginReach`: what is proved and what is left

The three open statements of `ChainCorrStartCopy.lean` and `ChainCorrStartRoot.lean` are
reduced here to smaller open statements. The files:

* `StartRootPartsBase.lean`: chains that reach the columns left of `cr` (`reach_of_first`,
  with the weak step correspondence `NextL`); matching raw parents in two canonical mountains
  (`left_match`).
* `StartRootPartsCols.lean`: the cells of the copies of `x₀`; the upper part of a copy of `x₀`
  has the raw parents of its origins (`upper_parent`, `upper_reach`).
* `StartRootPartsBlock0.lean`, `StartRootPartsB0.lean`: the block-`0` copy of `x₀`
  (`b0_profile`, `b0_step_lower`) and **`BoundaryChain` for `i = 1`** (`boundaryChain_one`).
* `StartRootPartsBoundary.lean`: `BoundaryChain` from `StepInner`, `BoundaryStepLower`,
  `BoundaryCutChain` (`boundaryChain_of_parts`).
* `StartRootPartsOrigin.lean`: **`OriginReach` when the origin of `pe` is in the upper part**
  (`originReach_upper`); `OriginReach` from `OriginLower` (`originReach_of_lower`).
* `StartRootPartsOriginLower.lean`: `OriginLower` from `PaLookup` and `X0Reach`.
* `StartRootPartsCutTop.lean`: **`CutTop` when `row pa = σ`**; `CutTop` from `CopyOrder`,
  `CopyFirst` and `GapTop` (`cutTop_of_gapTop`).

## The open statements

| statement | kind | used for |
|---|---|---|
| `BoundaryStepLower` | rule: one step from a lower non-gap node of a copy of `x₀`, block `≥ 1` | `BoundaryChain`, `i ≥ 2` |
| `BoundaryCutChain` | rule: `BoundaryChain` for gap copies, block `≥ 1` | `BoundaryChain`, `i ≥ 2` |
| `PaLookup` | rule: `pa` is the highest node of `cr` at or below the origin of `pe` | `OriginReach` |
| `X0Reach` | `M(s)` only | `OriginReach` |
| `GapTop` | rule: a gap copy of `pa` with `row pa < σ` needs `pa` on top of its column | `CutTop` |

plus the hypotheses `StepInner`, `CopyOrder`, `CopyFirst` (open elsewhere; `CopyEmitted` only for
`StartCopy`).

## Numerical tests (`reference/official/start-root-parts.cjs`)

Counts (node-scale pairs for `BoundaryStepLower` and `X0Reach`, node-scale-target triples for
`BoundaryCutChain` and `BoundaryChain1`, nodes otherwise). No failure in any sample.

| sample | `BoundaryStepLower` | `BoundaryCutChain` | `PaLookup` | `X0Reach` | `GapTop` | `OriginUpper` (proved) | `BoundaryChain1` (proved) |
|---|---:|---:|---:|---:|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 1296123 | 1119982 | 399180 | 334907 | 36 | 27774 | 3103914 |
| legal, length ≤ 6, entries ≤ 6 | 235539 | 0 | 174564 | 19123 | 0 | 10740 | 87240 |
| legal, length ≤ 5, entries ≤ 8 | 180690 | 1404 | 128010 | 12321 | 0 | 4326 | 60132 |
| random legal (`--random 20000,10,10,7`) | 778320 | 9756 | 504930 | 60211 | 78 | 27864 | 313647 |

`GapTop` counts only the nodes where it is not vacuous (a gap copy of `pa` exists and
`row pa < σ`); the case `row pa = σ` (proved) has 59400 / 19560 / 14754 / 63249 nodes.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs

/-- **`OriginReach`** from `PaLookup` and `X0Reach`. -/
theorem originReach_of_parts (hP : PaLookup) (hX : X0Reach) : OriginReach :=
  originReach_of_lower (originLower_of_parts hP hX)

/-- **`StartRoot`** from `StepInner` and the four open statements of this reduction. -/
theorem startRoot_of_open (hStep : StepInner) (hBL : BoundaryStepLower)
    (hBC : BoundaryCutChain) (hP : PaLookup) (hX : X0Reach) : StartRoot :=
  startRoot_of_parts (boundaryChain_of_parts hStep hBL hBC) (originReach_of_parts hP hX)

/-- **`StartCopy`** from the profile of a block and `GapTop`. -/
theorem startCopy_of_gapTop (hA : CopyOrder) (hB : CopyEmitted) (hC2 : CopyFirst)
    (hG : GapTop) : StartCopy :=
  startCopy_of_open hA hB hC2 (cutTop_of_gapTop hA hC2 hG)

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.boundaryChain_one
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.boundaryChain_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.originReach_upper
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.originReach_of_lower
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.originLower_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.originReach_of_parts
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.cutTop_of_gapTop
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.startRoot_of_open
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.startCopy_of_gapTop
