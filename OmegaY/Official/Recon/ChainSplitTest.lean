import OmegaY.Official.Recon.ChainSplit
import OmegaY.Official.Check

/-!
# The two open statements of `ChainSplit.lean` on the fixtures

Executable versions of `ParentBelowHolds` and `CrossChainHolds`, checked with `#guard` on
the 474 fixtures of `Check.lean`. For every real node `u = (c, i)` of a new column with a
node above it and stored parent `p` of that node:

* `parentBelowAt`: `row p ≤ row u`;
* `sameColumnAt`: if the candidate `Q u` (`Canonical.nextCandidate`) is in the column of
  `p`, then `Q u = p` (proved in `ChainSplit.lean` from the first statement; checked
  here as a sanity test);
* `crossAt`: if `Q u` is not in the column of `p`, the chain of stored parents from
  `Q u` reaches `p` through values `≥ v(u)` (`walk`, as in `Test.lean`).

These are finite checks of the exact statements, not a proof of them.
-/

namespace OmegaY.Official.Recon.ChainSplitTest

open Canonical

/-- The value of a cell (as in `Test.lean`). -/
def valueAt (R : Mountain) (r : Ref) : Nat :=
  match cellAt R r with
  | .ok cell => cell.value
  | .error _ => 0

/-- The stored parent of the node above `r` (as in `Test.lean`). -/
def rawParentRef (R : Mountain) (r : Ref) : Option Ref :=
  match R[r.column]? with
  | some col => match col[r.index + 1]? with
    | some up => up.left
    | none => none
  | none => none

/-- Walk the chain of stored parents from `q` to `p` through values `≥ th` (as in
`Test.lean`). -/
def walk (R : Mountain) (th : Nat) (p : Ref) : Nat → Ref → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, q, k =>
    if q = p then some k
    else if th ≤ valueAt R q then
      match rawParentRef R q with
      | some b => walk R th p fuel b (k + 1)
      | none => none
    else none

def parentBelowAt (R : Mountain) (c i : Nat) : Bool :=
  match rawParentRef R ⟨c, i⟩ with
  | none => true
  | some p =>
    match cellAt R p, cellAt R ⟨c, i⟩ with
    | .ok pc, .ok uc => decide (pc.row ≤ uc.row)
    | _, _ => false

def sameColumnAt (R : Mountain) (c i : Nat) : Bool :=
  match rawParentRef R ⟨c, i⟩ with
  | none => true
  | some p =>
    match nextCandidate R ⟨c, i⟩ with
    | .ok q => q.column != p.column || q == p
    | .error _ => false

/-- `0` when `Q u` is in the column of `p`, `1` when it is not and the chain condition holds,
`2` when it fails. -/
def crossAt (R : Mountain) (c i : Nat) : Nat :=
  match rawParentRef R ⟨c, i⟩ with
  | none => 0
  | some p =>
    match nextCandidate R ⟨c, i⟩ with
    | .ok q =>
      if q.column = p.column then 0
      else if (walk R (valueAt R ⟨c, i⟩) p (c + 1) q 0).isSome then 1 else 2
    | .error _ => 2

/-- The real non-top nodes of the new columns. -/
def newNodes (s : List Nat) (n : Nat) : Option (Mountain × List (Nat × Nat)) :=
  match Official.expandDiagram s n with
  | .ok R => some (R, ((List.range R.size).filter (s.length - 1 ≤ ·)).flatMap fun c =>
      match R[c]? with
      | some col => ((List.range col.size).filter (fun i => 0 < i ∧ i + 1 < col.size)).map
          fun i => (c, i)
      | none => [])
  | .error _ => none

def allB (s : List Nat) (n : Nat) (f : Mountain → Nat → Nat → Bool) : Bool :=
  match newNodes s n with
  | some (R, nodes) => nodes.all fun (c, i) => f R c i
  | none => false

def crossCount (s : List Nat) (n : Nat) : Nat :=
  match newNodes s n with
  | some (R, nodes) => (nodes.filter fun (c, i) => crossAt R c i = 1).length
  | none => 0

#guard Check.fixtures.all (fun f => allB f.1 f.2.1 parentBelowAt)
#guard Check.fixtures.all (fun f => allB f.1 f.2.1 sameColumnAt)
#guard Check.fixtures.all (fun f => allB f.1 f.2.1 (fun R c i => crossAt R c i != 2))

#eval
  let total := (Check.fixtures.map fun f =>
    match newNodes f.1 f.2.1 with | some (_, l) => l.length | none => 0).sum
  let cross := (Check.fixtures.map fun f => crossCount f.1 f.2.1).sum
  s!"{Check.fixtures.length} expansions, {total} new nodes with a node above; \
{cross} with the candidate outside the column of the parent"

end OmegaY.Official.Recon.ChainSplitTest
