[English](README-en.md) | [Japanese](README.md)

# wy-wo-por: well-foundedness of the official ω-Y (work in progress)

This repository aims to prove in Lean 4 that expansion in the official ω-Y sequence system is well-founded.

- The official ω-Y is defined by `expand` of Naruyoko's program [Study and Expand Sequence(仮)](https://naruyoko.github.io/StudyAndExpandSequence/) ([notes/00-survey.md](notes/00-survey.md), Japanese).
- Weak-magma ω-Y, proved by Phyrion, is a sequence system distinct from the official ω-Y. Its re-proof by patterns of resemblance is [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por).
- The two differ in the rule that fills the gap in a copied block (the magma) and in the rule that decides which nodes are lifted. Of the invariants of Phyrion's proof, the key bound of copied edges fails for the official ω-Y ([notes/01-feasibility.md](notes/01-feasibility.md), Japanese).
- The official expansion rule is written out, and differentially tested against the official program, in [notes/03-official-rule.md](notes/03-official-rule.md) (Japanese). Our own implementation is in [reference/official/](reference/official/).
- The Lean definition of the official expansion is `OmegaY.Official.expand` in [OmegaY/Official/Build.lean](OmegaY/Official/Build.lean). [OmegaY/Official/Check.lean](OmegaY/Official/Check.lean) compares it with 474 outputs of the official program.

## Status

Work in progress. Termination of the official ω-Y is not yet a theorem of this repository. The work is done on the branch `feature/official-expansion`.
