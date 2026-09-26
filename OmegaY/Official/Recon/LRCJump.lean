import OmegaY.Official.Recon.LRCBnd

/-!
# The jump law holds

`LowerRowsCopy` (`lowerRowsCopy_holds`, `LRCCopy.lean`) and `LowerRowsBoundary`
(`lowerRowsBoundary_holds`, `LRCBnd.lean`) are proved, so `jumpLawHolds_of_lowerRowsCases`
(`JumpLawLowerLeftDone.lean`) gives the jump law `RowLaw.JumpLawHolds` with no open hypothesis.
-/

namespace OmegaY.Official.Recon.LRC

/-- **The jump law of the output.** -/
theorem jumpLawHolds : RowLaw.JumpLawHolds :=
  LowerLeftDone.jumpLawHolds_of_lowerRowsCases lowerRowsCopy_holds lowerRowsBoundary_holds

end OmegaY.Official.Recon.LRC

#check (OmegaY.Official.Recon.LRC.lowerRowsCopy_holds :
  OmegaY.Official.Recon.JumpLawLower.LowerRowsCopy)
#check (OmegaY.Official.Recon.LRC.lowerRowsBoundary_holds :
  OmegaY.Official.Recon.JumpLawLower.LowerRowsBoundary)
#print axioms OmegaY.Official.Recon.LRC.lowerRowsCopy_holds
#print axioms OmegaY.Official.Recon.LRC.lowerRowsBoundary_holds
#print axioms OmegaY.Official.Recon.LRC.jumpLawHolds
