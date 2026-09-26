import OmegaY.Official.Recon.CrossLex
import OmegaY.Official.Check
import OmegaY.Official.Classification.Trace

/-!
# `CrossLexHolds` on the fixtures

An executable version of `CrossLexHolds` (`CrossLex.lean`), checked with `#guard` on the 474
fixtures of `Check.lean`. For every real node `u = (c, i)` of a new column with a node
`u⁺` above it and stored parent `p` of `u⁺`, when the candidate `q = Q u`
(`Canonical.nextCandidate`) is not in the column of `p`:

* `lastBefore` follows the stored parents from `q` to the node `c'` whose stored parent is
  `p` (it fails if the chain passes the column of `p` without meeting `p`);
* `row c'⁺ = row u⁺` and `Lex u⁺ c'⁺` (`lexB`, the executable `Lex`).

The count of these nodes by the origin kind of `u⁺` (`Classification.emitsT`: plain,
clean, cut = clean copy with a cut bottom, upper) is printed with `#eval`: plain 324,
clean 30, cut 0, upper 708 (of 1062).

It also checks `CutPred` (`CrossKinds.lean`) on the traced emitted list of every copied
column: every cut copy of a root-row node follows a copy of the same node with the same
emitted leg column.

These are finite checks, not a proof.
-/

namespace OmegaY.Official.Recon.CrossLexTest

open Canonical

/-- The stored parent of the node above `r` (as in `ChainSplitTest.lean`). -/
def rawParentRef (R : Mountain) (r : Ref) : Option Ref :=
  match R[r.column]? with
  | some col => match col[r.index + 1]? with
    | some up => up.left
    | none => none
  | none => none

/-- The real non-top nodes of the new columns (as in `ChainSplitTest.lean`). -/
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

/-- The cell above `r`. -/
def upperCell (R : Mountain) (r : Ref) : Option Cell :=
  match R[r.column]? with
  | some col => col[r.index + 1]?
  | none => none

/-- The executable `Lex z w`. -/
def lexB (R : Mountain) : Nat → Ref → Ref → Bool
  | 0, _, _ => false
  | fuel + 1, z, w =>
    match upperCell R z with
    | none => true
    | some zu =>
      match upperCell R w with
      | none => false
      | some wu =>
        match zu.left, wu.left with
        | some a, some b =>
          if a.column < b.column then true
          else if a = b ∧ zu.row = wu.row then
            lexB R fuel ⟨z.column, z.index + 1⟩ ⟨w.column, w.index + 1⟩
          else false
        | _, _ => false

/-- The node `c'` of the chain of stored parents from `q` whose stored parent is `p`. -/
def lastBefore (R : Mountain) (p : Ref) : Nat → Ref → Option Ref
  | 0, _ => none
  | fuel + 1, q =>
    match rawParentRef R q with
    | none => none
    | some b =>
      if b = p then some q
      else if b.column < p.column then none
      else lastBefore R p fuel b

/-- `0`: not a cross node; `1`: a cross node satisfying `CrossLexHolds`; `2`: a failure. -/
def crossLexAt (R : Mountain) (c i : Nat) : Nat :=
  match rawParentRef R ⟨c, i⟩ with
  | none => 0
  | some p =>
    match nextCandidate R ⟨c, i⟩ with
    | .error _ => 2
    | .ok q =>
      if q.column = p.column then 0
      else
        match lastBefore R p (c + 1) q with
        | none => 2
        | some c' =>
          match upperCell R ⟨c, i⟩, upperCell R c' with
          | some uu, some cu =>
            if uu.row = cu.row ∧ lexB R 1000 ⟨c, i + 1⟩ ⟨c'.column, c'.index + 1⟩ then 1 else 2
          | _, _ => 2

#guard Check.fixtures.all (fun f => allB f.1 f.2.1 (fun R c i => crossLexAt R c i != 2))

/-! ## The origin kind of `u⁺` -/

/-- The traced emitted list of the call of `copyColumn` that made column `X`. -/
def emitsAt (s : List Nat) (R : Mountain) (X : Nat) :
    Option (List (Emit × Classification.Origin)) :=
  match Canonical.build s with
  | .error _ => none
  | .ok M =>
    let x0 := M.size - 1
    match M[x0]? with
    | none => none
    | some lastCol =>
      match lastCol.back? with
      | none => none
      | some t =>
        match t.left with
        | none => none
        | some root =>
          let cr := root.column
          let w := x0 - cr
          let i := if X = x0 then 0 else (X - cr - 1) / w
          let x := X - w * i
          let ctx : Context := ⟨M, R.extract 0 X, x, i, cr, w, x0⟩
          match Classification.emitsT ctx (official t.row) with
          | .error _ => none
          | .ok es => some es

/-- The kind of the origin of the node `(X, j + 1)`: `0` plain, `1` clean, `2` cut,
`3` upper, `4` unknown. -/
def kindAt (s : List Nat) (R : Mountain) (X j : Nat) : Nat :=
  match emitsAt s R X with
  | none => 4
  | some es =>
    match es[j]? with
    | some (_, .plain _) => 0
    | some (_, .clean _ false) => 1
    | some (_, .clean _ true) => 2
    | some (_, .upper _) => 3
    | none => 4

/-- The executable `CutPred` (`CrossKinds.lean`). -/
def cutPredB (es : List (Emit × Classification.Origin)) : Bool :=
  (List.range es.length).all fun j =>
    match es[j]? with
    | some (em, .clean r true) =>
      match j, es[j - 1]? with
      | 0, _ => false
      | _ + 1, some (em', .clean r' _) => r' == r && em'.leftColumn == em.leftColumn
      | _, _ => false
    | _ => true

/-- `CutPred` for every copied column of `s[n]`. -/
def cutPredAll (s : List Nat) (n : Nat) : Bool :=
  match Official.expandDiagram s n with
  | .error _ => false
  | .ok R =>
    ((List.range R.size).filter (s.length - 1 ≤ ·)).all fun X =>
      match emitsAt s R X with
      | some es => cutPredB es
      | none => false

#guard Check.fixtures.all (fun f => cutPredAll f.1 f.2.1)

/-- The number of cut emits in the copied columns of `s[n]`. -/
def cutCount (s : List Nat) (n : Nat) : Nat :=
  match Official.expandDiagram s n with
  | .error _ => 0
  | .ok R =>
    (((List.range R.size).filter (s.length - 1 ≤ ·)).map fun X =>
      match emitsAt s R X with
      | some es => (es.filter fun e => match e.2 with
          | .clean _ true => true
          | _ => false).length
      | none => 0).sum

#eval s!"cut emits in the fixtures: {(Check.fixtures.map fun f => cutCount f.1 f.2.1).sum}"

/-- The number of cross nodes whose `u⁺` has origin kind `k`. -/
def crossKindCount (s : List Nat) (n : Nat) (k : Nat) : Nat :=
  match newNodes s n with
  | some (R, nodes) =>
    (nodes.filter fun (c, i) => crossLexAt R c i = 1 && kindAt s R c i = k).length
  | none => 0

#eval
  let count := fun k => (Check.fixtures.map fun f => crossKindCount f.1 f.2.1 k).sum
  s!"cross nodes by the origin kind of u⁺: plain {count 0}, clean {count 1}, \
cut {count 2}, upper {count 3}, unknown {count 4}"

end OmegaY.Official.Recon.CrossLexTest
