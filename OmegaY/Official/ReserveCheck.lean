import OmegaY.Official.Check
import OmegaY.Official.Reserve

/-!
# The splice classification on the fixtures

For every fixture `(s, n, t)` of `Check.lean`, `classifiedB s n D` evaluates to
`true` with `D` the largest degree of a row of `M(s)` and `M(t)`: every leg atom of
`M(s[n])` is a base, reserve or seam atom for the leg atoms of `M(s)`
(`notes/04-official-design.md` §1.2, §3).

For comparison, Phyrion's representation (real edges only, `classifiedEdgesB`)
fails on `(1,3,3)[2]` and on other fixtures.

These are finite executable checks, not a proof about other inputs.
-/

namespace OmegaY.Official.Reserve.Check

open OmegaY.Official.Check

def dimension (f : Fixture) : Nat := max (dimOf f.1) (dimOf f.2.2)

def legClassified (f : Fixture) : Bool := classifiedB f.1 f.2.1 (dimension f)

def edgeClassified (f : Fixture) : Bool := classifiedEdgesB f.1 f.2.1 (dimension f)

#guard legClassified ([1, 3, 3], 2, [1, 3, 2, 5, 7, 12])
#guard !edgeClassified ([1, 3, 3], 2, [1, 3, 2, 5, 7, 12])
#guard legClassified ([1, 3, 2, 5, 7, 12, 19, 25, 30], 1,
  [1, 3, 2, 5, 7, 12, 19, 25, 29, 38, 54, 69])
#guard fixtures.all legClassified

#eval s!"{fixtures.length} expansions: leg atoms classified {(fixtures.filter legClassified).length}, \
real edges classified {(fixtures.filter edgeClassified).length}"

end OmegaY.Official.Reserve.Check
