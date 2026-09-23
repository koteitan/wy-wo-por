import OmegaY.Official.Build
import OmegaY.Official.Check
import OmegaY.Official.Reserve
import OmegaY.Official.ReserveCheck
import OmegaY.Official.Descent
import OmegaY.Official.Dimension
import OmegaY.Official.Reconstruction
import OmegaY.Official.Classification.Bridge
import OmegaY.Official.Classification.Proofs.ControlDominates
import OmegaY.Official.Recon.FirstEmit

/-! The official omega-Y expansion (notes/03-official-rule.md): the executable
definition `OmegaY.Official.expand` and its fixtures against the official
program; the leg atoms and the splice classification (notes/04-official-design.md)
and their check on the same fixtures; the well-foundedness of the official
expansion from the degree bound and the atom classification
(`Reconstruction.wellFounded_of_parts`); the dimension bound (`Dimension`). -/
