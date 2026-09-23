[English](README-en.md) | [Japanese](README.md)

# wy-wo-por: well-foundedness of the official ω-Y (work in progress)

This repository aims to prove in Lean 4 that expansion in the official ω-Y sequence system is well-founded.

- The official ω-Y is defined by `expand` of Naruyoko's program [Study and Expand Sequence(仮)](https://naruyoko.github.io/StudyAndExpandSequence/) ([notes/00-survey.md](notes/00-survey.md), Japanese).
- Weak-magma ω-Y, proved by Phyrion, is a sequence system distinct from the official ω-Y. Its re-proof by patterns of resemblance is [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por).
- The two differ only in the rule that fills the gap in a copied block (the magma). Of the invariants of Phyrion's proof, the key bound of copied edges fails for the official ω-Y ([notes/01-feasibility.md](notes/01-feasibility.md), Japanese).

## Status

Work in progress. Termination of the official ω-Y is not yet a theorem of this repository. The work is done on the branch `feature/official-expansion`.
