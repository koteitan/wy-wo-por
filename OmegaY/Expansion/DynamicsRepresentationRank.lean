/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DynamicsRepresentationRank.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.RepresentedMountain
import OmegaY.Expansion.SupportedDimension
import OmegaY.Expansion.GeneratedWellOrder

/-!
Ordinal accessibility from representation descent for the actual dynamics.

The descent hypothesis below is deliberately explicit: this file does not
prove the positive-copy representation splice. Initial representations,
canonical reconstruction, dimension preservation, and the ordinal induction
are all supplied here or by the executable theorems already imported.

Each starting expression chooses its own finite dimension. The induction
uses an upper bound on all column labels, so an empty child needs no last
label, and the empty input's total-program self-loop is excluded by `Step`.
-/

namespace OmegaY.Expansion.Dynamics

open Canonical Geometry Frame

abbrev Representation (s : Expr) (D : Nat) :=
  KeyRepresentation (diagram_normal s).toOrdered D

theorem diagram_nonempty {s : Expr} (hNonempty : s.val ≠ []) : 0 < (diagram s).size := by
  rw [build_size (diagram_build s)]
  exact List.length_pos_iff.mpr hNonempty

/-- The sole local semantic decrease obligation at a fixed supported
dimension. It refers to the actual total `next`, not an abstract successor. -/
def RepresentationDescent (D : Nat) : Prop :=
  ∀ (s : Expr), KeyDimension s D → ∀ (old : Representation s D) (copies : Nat)
    (hNonempty : s.val ≠ []),
    ∃ fresh : Representation (next s copies) D,
      ∀ column, fresh.labels column < old.lastLabel (diagram_nonempty hNonempty)

/-- A direct interface for the final executable representation theorem.
The input mountain is the actual successful canonical build, and the
output mountain is the actual successful expansion diagram. -/
def ActualRepresentationDescent : Prop :=
  ∀ {input : List Nat} {initial result : Mountain} {copies D : Nat}
    (hBuild : Canonical.build input = .ok initial) (_hNonempty : input ≠ [])
    (_hDimension : MountainKeyDimension initial D)
    (hRun : expandDiagram input copies = .ok result)
    (old : KeyRepresentation (build_normal_of_success hBuild).toOrdered D),
    ∃ (hWidth : 0 < initial.size)
      (fresh : KeyRepresentation
        (expandDiagram_valid_of_success (build_success_legal hBuild) hRun).toOrdered D),
      ∀ column, fresh.labels column < old.lastLabel hWidth

theorem ActualRepresentationDescent.on_dimension
    (hDescent : ActualRepresentationDescent) (D : Nat) : RepresentationDescent D := by
  intro s hDimension old copies hNonempty
  obtain ⟨_hWidth, fresh, hBelow⟩ := hDescent (diagram_build s) hNonempty hDimension
    (next_diagram_run s copies) old
  exact ⟨fresh, hBelow⟩

theorem empty_accessible {s : Expr} (hEmpty : s.val = []) : Acc Step s := by
  refine Acc.intro s ?_
  intro child hStep
  exact (no_step_from_empty hEmpty hStep).elim

/-- Induction is on an actual bounded ordinal label. The child mountain's
dimension is recovered from the executable step; no uniform dimension over
all legal expressions and no accessibility hypothesis occur here. -/
theorem accessible_of_representation_below (D : Nat) (hDescent : RepresentationDescent D)
    (alpha : Model.Label) :
    ∀ (s : Expr), KeyDimension s D → ∀ old : Representation s D,
      Reflection.Bounded old.labels alpha → Acc Step s := by
  refine (show WellFounded ((· < ·) : Model.Label → Model.Label → Prop) from wellFounded_lt).induction
    (C := fun bound => ∀ (s : Expr), KeyDimension s D → ∀ old : Representation s D,
      Reflection.Bounded old.labels bound → Acc Step s) alpha ?_
  intro alpha ih s hDimension old hBound
  refine Acc.intro s ?_
  rintro child ⟨hNonempty, copies, rfl⟩
  obtain ⟨fresh, hFresh⟩ := hDescent s hDimension old copies hNonempty
  have hLast : old.lastLabel (diagram_nonempty hNonempty) < alpha :=
    hBound ⟨(diagram s).size - 1, by
      change (diagram s).size - 1 < (diagram s).size
      have := diagram_nonempty hNonempty
      omega⟩
  exact ih (old.lastLabel (diagram_nonempty hNonempty)) hLast (next s copies)
    (next_key_dimension hDimension copies) fresh hFresh

/-- Initial representability is proved for the actual finite mountain.
Only the semantic successor construction remains a parameter. -/
theorem accessible_of_key_dimension {D : Nat} (hDescent : RepresentationDescent D)
    {s : Expr} (hDimension : KeyDimension s D) : Acc Step s := by
  obtain ⟨old⟩ := keyRepresentation_exists (diagram_normal s).toOrdered D
  exact accessible_of_representation_below D hDescent Reflection.OrdinalSupply.top
    s hDimension old old.bounded

theorem step_wellFounded_on_dimension (D : Nat) (hDescent : RepresentationDescent D) :
    WellFounded (fun child parent : {s : Expr // KeyDimension s D} => Step child.val parent.val) := by
  refine ⟨fun s => ?_⟩
  exact InvImage.accessible (fun t : {s : Expr // KeyDimension s D} => t.val)
    (accessible_of_key_dimension hDescent s.property)

theorem key_dimension_exists (s : Expr) : ∃ D : Nat, KeyDimension s D := by
  obtain ⟨D, hDimension⟩ := fixed_dimension_for_descendants s
  exact ⟨D, hDimension s (.refl s)⟩

/-- Dimensions are chosen separately for each initial legal expression.
This is conditional on the displayed descent theorem, not a closed proof
of omega-Y well-foundedness. -/
theorem step_wellFounded_of_representation_descent
    (hDescent : ∀ D, RepresentationDescent D) : WellFounded Step := by
  refine ⟨fun s => ?_⟩
  obtain ⟨D, hDimension⟩ := key_dimension_exists s
  exact accessible_of_key_dimension (hDescent D) hDimension

theorem step_wellFounded_of_actual_representation_descent
    (hDescent : ActualRepresentationDescent) : WellFounded Step :=
  step_wellFounded_of_representation_descent hDescent.on_dimension

/-- The already-proved prefix/reachability argument then applies to the
standard generated domain. Its domain is not silently enlarged to the
lexicographic order on unrelated arbitrary legal inputs. -/
theorem generated_isWellOrder_of_actual_representation_descent
    (hDescent : ActualRepresentationDescent) :
    IsWellOrder GeneratedExpr (fun a b => Lex a.val b.val) :=
  generated_isWellOrder (step_wellFounded_of_actual_representation_descent hDescent)

theorem every_legal_root_isWellOrder_of_actual_representation_descent
    (hDescent : ActualRepresentationDescent) (root : Expr) :
    IsWellOrder (Descendant root) (fun a b => Lex a.val b.val) :=
  every_legal_root_isWellOrder (step_wellFounded_of_actual_representation_descent hDescent) root

end OmegaY.Expansion.Dynamics

#print axioms OmegaY.Expansion.Dynamics.accessible_of_representation_below
#print axioms OmegaY.Expansion.Dynamics.step_wellFounded_of_actual_representation_descent
#print axioms OmegaY.Expansion.Dynamics.generated_isWellOrder_of_actual_representation_descent
