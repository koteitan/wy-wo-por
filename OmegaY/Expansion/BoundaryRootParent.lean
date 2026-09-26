/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BoundaryRootParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.AppendLocality
import OmegaY.Rows.EdgeTransport

/-!
# Exact parent selection in the copied root boundary

When the source parent is the root-row node itself, its moved column is a
block boundary. Its selected target is already the greatest node below the
reference cap. Lowering that ceiling within the same gap preserves the
actual selection, without postulating a new boundary adjacency.
-/

namespace OmegaY.Expansion

open Canonical

theorem below_lower_ceiling {mountain : Mountain} {column : Nat} {nodes : Column}
    (hNodes : mountain[column]? = some nodes) {oldCeiling newCeiling : Row} {ref : Ref}
    (hBelow : below mountain column oldCeiling = .ok ref) {cell : Cell}
    (hRead : nodes[ref.index]? = some cell) (hLow : cell.row < newCeiling)
    (hHigh : newCeiling ≤ oldCeiling) : below mountain column newCeiling = .ok ref := by
  obtain ⟨found, hFound⟩ := (below_succeeds_iff hNodes newCeiling).mpr ⟨ref.index, cell, hRead, hLow⟩
  obtain ⟨hFoundColumn, foundCell, hFoundRead, hFoundRow⟩ := below_result hNodes hFound
  have hFoundGe := below_max_index hNodes hFound hRead hLow
  have hFoundLe := below_max_index hNodes hBelow hFoundRead (hFoundRow.trans_le hHigh)
  have hRefColumn := (below_result hNodes hBelow).1
  have he : found = ref := by
    cases found
    cases ref
    simp only [Ref.mk.injEq]
    constructor <;> dsimp only at * <;> omega
  simpa only [he] using hFound

/-- The reference cap also bounds the exact lifted B row when the parent
is the root row. The lifted B row lies strictly above the actual selected
target, so the same concrete boundary reference is selected. -/
theorem below_boundary_root_parent {mountain : Mountain} {column : Nat} {nodes : Column}
    (hNodes : mountain[column]? = some nodes) {root child : Row} {degree : Nat}
    {ref : Ref} (hBelow : below mountain column (Row.bump root degree) = .ok ref)
    {cell : Cell} (hRead : nodes[ref.index]? = some cell)
    (hRootTarget : root ≤ cell.row) (hRootChild : root ≤ child)
    (hChildCap : child < Row.bump root degree) :
    below mountain column (Row.lift root cell.row (Row.B child root)) = .ok ref ∧
      Row.lift root cell.row (Row.B child root) =
        Row.B (Row.lift root cell.row child) cell.row := by
  obtain ⟨_, found, hFoundRead, hFoundCap⟩ := below_result hNodes hBelow
  have he : found = cell := Option.some.inj (hFoundRead.symm.trans hRead)
  subst found
  have hLift := Row.lift_mem_interval hRootTarget hFoundCap hRootChild hChildCap
  have hTargetLow : cell.row ≤ Row.lift root cell.row child := by
    have h := Row.lift_monotone (root := root) (t := cell.row) le_rfl hRootChild
    simpa only [Row.lift_at_root] using h
  have hEquation : Row.lift root cell.row (Row.B child root) =
      Row.B (Row.lift root cell.row child) cell.row := by
    rw [Row.lift_B hRootChild le_rfl, Row.lift_at_root]
  have hLow : cell.row < Row.lift root cell.row (Row.B child root) := by
    rw [hEquation]
    exact hTargetLow.trans_lt (Row.lt_B _ _)
  have hHigh : Row.lift root cell.row (Row.B child root) ≤ Row.bump root degree := by
    rw [hEquation]
    exact Row.B_le_cap_of_same_interval hLift.1 hLift.2 hRootTarget hFoundCap
  exact ⟨below_lower_ceiling hNodes hBelow hRead hLow hHigh, hEquation⟩

theorem below_boundary_root_parent_preserved {before after : Mountain}
    (hPreserve : PreservesColumns before after) {column : Nat} {nodes : Column}
    (hNodes : before[column]? = some nodes) {root child : Row} {degree : Nat}
    {ref : Ref} (hBelow : below before column (Row.bump root degree) = .ok ref)
    {cell : Cell} (hRead : nodes[ref.index]? = some cell)
    (hRootTarget : root ≤ cell.row) (hRootChild : root ≤ child)
    (hChildCap : child < Row.bump root degree) :
    below after column (Row.lift root cell.row (Row.B child root)) = .ok ref := by
  have hBefore := (below_boundary_root_parent hNodes hBelow hRead hRootTarget hRootChild hChildCap).1
  exact (hPreserve.below (Array.getElem?_eq_some_iff.mp hNodes).1 _).trans hBefore

#print axioms below_lower_ceiling
#print axioms below_boundary_root_parent
#print axioms below_boundary_root_parent_preserved

end OmegaY.Expansion
