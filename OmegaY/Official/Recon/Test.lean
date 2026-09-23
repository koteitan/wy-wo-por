import OmegaY.Official.Recon.Search
import OmegaY.Official.Check

/-!
# The open statements on the fixtures

Executable versions of the statements about the new columns, checked with `#guard` on
the 474 fixtures of `Check.lean` (the expansions compared with the official program):

* `bottomB`, `geometryB`: `BottomOK` and `Expansion.ColumnParentGeometry` (the statements
  `BottomHolds` and `NewGeometryHolds` of `Reduction.lean`; the latter contains the row
  law `RowLawHolds`). `BottomHolds` is proved (`FirstEmit.bottomHolds`).
* `chainLen`: the chain condition `ChainOK` of `Search.lean` (`ChainHolds`), with the
  length of the chain of stored parents from `Q u` to the stored parent.

These are finite checks of the exact statements, not a proof of them.
-/

namespace OmegaY.Official.Recon.Test

open Canonical

/-- `BottomOK c col` as a Boolean. -/
def bottomB (c : Nat) (col : Column) : Bool :=
  match col[1]? with
  | some b => b.row == 1 && b.left == some ⟨c - 1, 0⟩
  | none => false

/-- One adjacent pair `(lower, upper)` at `index` of column `c` satisfies the parent
geometry. -/
def pairB (R : Mountain) (c index : Nat) (lower upper : Cell) : Bool :=
  match upper.left with
  | none => false
  | some ref =>
    match cellAt R ref, findParent R ⟨c, index⟩ with
    | .ok parent, .ok found => found == ref && upper.row == Row.B lower.row parent.row
    | _, _ => false

/-- `ColumnParentGeometry R c col` as a Boolean. -/
def geometryB (R : Mountain) (c : Nat) (col : Column) : Bool :=
  (List.range col.size).all fun index =>
    index == 0 ||
      match col[index]?, col[index + 1]? with
      | some lower, some upper => pairB R c index lower upper
      | _, _ => true

/-- The number of new real nodes with a node above (the checked pairs). -/
def pairsIn (x0 : Nat) (R : Mountain) : Nat :=
  ((List.range R.size).filter (x0 ≤ ·)).foldl (fun acc c =>
    acc + match R[c]? with | some col => col.size - 2 | none => 0) 0

/-- Both statements for the new columns of one expansion. -/
def newColumnsB (s : List Nat) (n : Nat) : Bool :=
  match Official.expandDiagram s n with
  | .ok R => (List.range R.size).all fun c =>
      decide (c < s.length - 1) ||
        match R[c]? with
        | some col => bottomB c col && geometryB R c col
        | none => false
  | .error _ => false

def pairsOf (s : List Nat) (n : Nat) : Nat :=
  match Official.expandDiagram s n with
  | .ok R => pairsIn (s.length - 1) R
  | .error _ => 0

/-- The value of a cell. -/
def valueAt (R : Mountain) (r : Ref) : Nat :=
  match cellAt R r with
  | .ok cell => cell.value
  | .error _ => 0

/-- The stored parent of the node above `r`. -/
def rawParentRef (R : Mountain) (r : Ref) : Option Ref :=
  match R[r.column]? with
  | some col => match col[r.index + 1]? with
    | some up => up.left
    | none => none
  | none => none

/-- Walk the chain of stored parents from `q` to `p` through values `≥ th`; returns the
number of steps. -/
def walk (R : Mountain) (th : Nat) (p : Ref) : Nat → Ref → Nat → Option Nat
  | 0, _, _ => none
  | fuel + 1, q, k =>
    if q = p then some k
    else if th ≤ valueAt R q then
      match rawParentRef R q with
      | some b => walk R th p fuel b (k + 1)
      | none => none
    else none

/-- `ChainOK` at node `(c, i)` as the length of the chain (`none` if it fails). -/
def chainLen (R : Mountain) (c i : Nat) : Option Nat :=
  match rawParentRef R ⟨c, i⟩ with
  | none => some 0
  | some p =>
    match nextCandidate R ⟨c, i⟩ with
    | .ok q => walk R (valueAt R ⟨c, i⟩) p (c + 1) q 0
    | .error _ => none

/-- The chain lengths of all real non-top nodes of the new columns. -/
def chainLens (s : List Nat) (n : Nat) : Option (List Nat) :=
  match Official.expandDiagram s n with
  | .ok R =>
    ((List.range R.size).filter (s.length - 1 ≤ ·)).foldlM (fun acc c =>
      match R[c]? with
      | some col => ((List.range col.size).filter (fun i => 0 < i ∧ i + 1 < col.size)).foldlM
          (fun acc i => (chainLen R c i).map (· :: acc)) acc
      | none => none) []
  | .error _ => none

def chainB (s : List Nat) (n : Nat) : Bool := (chainLens s n).isSome

#guard newColumnsB [1, 3, 3] 2
#guard chainB [1, 3, 3] 2
#guard Check.fixtures.all (fun f => chainB f.1 f.2.1)

#eval
  let lens := (Check.fixtures.filterMap (fun f => chainLens f.1 f.2.1)).flatten
  s!"ChainOK holds on {(Check.fixtures.filter (fun f => chainB f.1 f.2.1)).length} expansions; \
{lens.length} new nodes, chain length 0: {(lens.filter (· = 0)).length}, 1: \
{(lens.filter (· = 1)).length}, 2: {(lens.filter (· = 2)).length}, ≥ 3: \
{(lens.filter (3 ≤ ·)).length}"
#guard Check.fixtures.all (fun f => newColumnsB f.1 f.2.1)

#eval s!"{Check.fixtures.length} expansions: BottomOK and the parent geometry hold on \
{(Check.fixtures.filter (fun f => newColumnsB f.1 f.2.1)).length}; \
{(Check.fixtures.map (fun f => pairsOf f.1 f.2.1)).sum} new parent-geometry pairs checked"

end OmegaY.Official.Recon.Test
