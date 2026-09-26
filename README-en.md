[English](README-en.md) | [Japanese](README.md)

# wy-wo-por: well-foundedness of the official ω-Y

This repository proves in Lean 4 that expansion in the official ω-Y sequence system is well-founded.

- The official ω-Y is defined by `expand` of Naruyoko's program [Study and Expand Sequence(仮)](https://naruyoko.github.io/StudyAndExpandSequence/) ([notes/00-survey.md](notes/00-survey.md), Japanese).
- Weak-magma ω-Y, proved by Phyrion, is a sequence system distinct from the official ω-Y. Its re-proof by patterns of resemblance is [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por).
- The two differ in the rule that fills the gap in a copied block (the magma) and in the rule that decides which nodes are lifted. Of the invariants of Phyrion's proof, the key bound of copied edges fails for the official ω-Y ([notes/01-feasibility.md](notes/01-feasibility.md), Japanese).
- The official expansion rule is written out, and differentially tested against the official program, in [notes/03-official-rule.md](notes/03-official-rule.md) (Japanese). Our own implementation is in [reference/official/](reference/official/).
- The Lean definition of the official expansion is `OmegaY.Official.expand` in [OmegaY/Official/Build.lean](OmegaY/Official/Build.lean). [OmegaY/Official/Check.lean](OmegaY/Official/Check.lean) compares it with 474 outputs of the official program.
- The proof design is in [notes/04-official-design.md](notes/04-official-design.md) (Japanese). Phyrion's reflection theorem is used as it is, and the atoms of the representation are replaced by one "leg atom" per node. With these atoms, the classification that the reflection needs held on every expansion we tested ([reference/official/reserve.cjs](reference/official/reserve.cjs)). In Lean, the atom system and the classification check are defined in [OmegaY/Official/Reserve.lean](OmegaY/Official/Reserve.lean), and [OmegaY/Official/ReserveCheck.lean](OmegaY/Official/ReserveCheck.lean) evaluates the check to true on 474 expansions. [OmegaY/Official/Reconstruction.lean](OmegaY/Official/Reconstruction.lean) proves well-foundedness of the official expansion assuming two things (`OmegaY.Official.Reconstruction.wellFounded_of_parts` from `DegreeAndAtomsHold`): the output mountain has degree at most $`D`$, and every leg atom of the output is classified. The degree part is proved in [OmegaY/Official/Dimension.lean](OmegaY/Official/Dimension.lean) assuming the reconstruction of the output mountain (`ReconstructionHolds`). The output length, and that the output mountain can be built, are proved. The hypothesis used first, `Descent.ClassificationHolds`, was false because of the empty sequence (`not_classificationHolds`), so it was restated for nonempty sequences.
- Background notes for reading the proof are in [study/](study/en/README.md): ordinals, well-founded recursion, Σ₁ elementary substructures, patterns of resemblance, the ω-Y mountain and expansion, and the route of the proof.

## Status

Well-foundedness of the official ω-Y expansion is proved with no hypothesis (v0.1.38).

- Theorem: `OmegaY.Official.Recon.FinalStageF.wellFounded_step : WellFounded Descent.Step` in [OmegaY/Official/Recon/FinalStageF.lean](OmegaY/Official/Recon/FinalStageF.lean).
  - `Descent.Step t s` says that s is nonempty and `expand s n = .ok t` for some n.
  - Restated as `no_infinite_expansion`: from any sequence, expansion cannot go on forever.
- `#print axioms` gives only `[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no new axiom and no `native_decide`.
- The hypotheses found false on the way, and how they were replaced, are in [notes/04-official-design.md](notes/04-official-design.md) §6.1 and [notes/06-final-assembly.md](notes/06-final-assembly.md) (Japanese).
- The work was done on the branch `feature/official-expansion`.
- This proof is ported to Lean 4.30.0 in [Notation/OmegaY](https://github.com/koteitan/googology-lean/tree/feature/trio-pair/Googology/Notation/OmegaY) of [koteitan/googology-lean](https://github.com/koteitan/googology-lean).
