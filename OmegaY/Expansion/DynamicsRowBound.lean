/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DynamicsRowBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualCanonicalReconstruction
import OmegaY.Expansion.LegalDynamics
import OmegaY.Expansion.FiniteDegree

/-!
# One fixed finite row dimension along every actual expansion path

Exact canonical reconstruction identifies the diagram used by the next
expansion with the stored diagram returned by the previous expansion.
Consequently the existing single-expansion row bound is now an invariant
of arbitrarily long finite execution paths. The finite dimension depends
only on the starting expression, not on path length or any copy count.
This invariant alone does not exclude an infinite path.
-/

namespace OmegaY.Expansion.Dynamics

open Canonical Geometry Frame

noncomputable def diagram (s : Expr) : Mountain :=
  Classical.choose (build_total s.property)

theorem diagram_build (s : Expr) : Canonical.build s.val = .ok (diagram s) :=
  (Classical.choose_spec (build_total s.property)).1

theorem diagram_normal (s : Expr) : (Frame.ofMountain (diagram s)).Normal :=
  build_normal_of_success (diagram_build s)

/-- This identifies the next actual canonical mountain, not only its
bottom values or an isomorphic graph. -/
theorem next_diagram_run (s : Expr) (copies : Nat) :
    expandDiagram s.val copies = .ok (diagram (next s copies)) := by
  obtain ⟨output, mountain, hDiagram, hExpand, _, hBuild, _⟩ := expand_total_canonical s.property copies
  have hValues := next_eq_of_run hExpand
  have hNextBuild := diagram_build (next s copies)
  rw [hValues] at hNextBuild
  have he : mountain = diagram (next s copies) := Except.ok.inj (hBuild.symm.trans hNextBuild)
  exact he ▸ hDiagram

def RowsBound (s : Expr) (height : Row) : Prop := MountainRowsBound (diagram s) height

theorem next_rows_bound {s : Expr} {height : Row} (hBound : RowsBound s height) (copies : Nat) :
    RowsBound (next s copies) height :=
  expandDiagram_rows_bound (diagram_build s) hBound (next_diagram_run s copies)

theorem Step.rows_bound {child parent : Expr} (step : Step child parent)
    {height : Row} (hBound : RowsBound parent height) : RowsBound child height := by
  obtain ⟨_, copies, rfl⟩ := step
  exact next_rows_bound hBound copies

theorem Path.rows_bound {root output : Expr} (path : Path root output)
    {height : Row} (hBound : RowsBound root height) : RowsBound output height := by
  induction path with
  | refl => exact hBound
  | tail prior copies _ ih => exact next_rows_bound ih copies

/-- The original maximum ordinal row bounds every node in every later
canonical mountain, for arbitrary finite choices at every step. -/
theorem Path.initial_ceiling {root output : Expr} (path : Path root output) :
    RowsBound output (rowCeiling (diagram root)) :=
  path.rows_bound (rowCeiling_bound (diagram root))

theorem Path.initial_exponent_bound {root output : Expr} (path : Path root output)
    {ref : Ref} {cell : Cell} (hRead : Canonical.cellAt (diagram output) ref = .ok cell) :
    Row.jump 0 cell.row ≤ exponentBound (diagram root) ∧
      ∀ i, exponentBound (diagram root) ≤ i → Row.coeff cell.row i = 0 := by
  have hRow := path.initial_ceiling ref cell hRead
  exact ⟨Row.jump_zero_monotone hRow, fun _ hi => Row.coeff_zero_above_bound hRow hi⟩

theorem fixed_dimension_for_descendants (root : Expr) :
    ∃ D : Nat, ∀ output, Path root output →
      ∀ node : (Frame.ofMountain (diagram output)).Node,
        ∀ i, D < i → Row.coeff ((Frame.ofMountain (diagram output)).height node) i = 0 := by
  refine ⟨exponentBound (diagram root), ?_⟩
  intro output path node i hi
  exact (path.initial_exponent_bound (Canonical.cellAt_of_frame_node (diagram output) node)).2 i hi.le

end OmegaY.Expansion.Dynamics

#print axioms OmegaY.Expansion.Dynamics.next_diagram_run
#print axioms OmegaY.Expansion.Dynamics.next_rows_bound
#print axioms OmegaY.Expansion.Dynamics.Path.rows_bound
#print axioms OmegaY.Expansion.Dynamics.Path.initial_exponent_bound
#print axioms OmegaY.Expansion.Dynamics.fixed_dimension_for_descendants
