/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourCanonicalRows.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ContourPowerSteps
import OmegaY.Expansion.FrozenSource
import OmegaY.Rows.EdgeTransport

/-!
# Exact B rows for actual fixed-left contour edges leaving a lift interval

This closes a nontrivial local contour case. The lower source row lies in
`[root, bump root scale)`, its stored father lies at or below `root` in a
column strictly before the copy root, and its original upper row reaches
the cap. The lower copy can move while the upper and the father stay fixed.
The theorem concerns the actual contour head and its actual stored reference.
The wrapper obtains the original B rule from an actual canonical source build.

The root/cap geometry remains explicit input; it is not a renamed output B
claim. Deriving this case classification for every actual source edge needs
the weak-cone interval barrier. In the shifted-parent case, current dynamic
state additionally lacks the effective parent's actual row together with
the next-parent-row cutoff. Power steps and marker/target occurrence alone
do not identify the strict-below endpoint with the lift of the old parent.
-/

namespace OmegaY.Expansion

open Canonical

/-- The fixed branch of the real edge copier, retaining the exact old Ref. -/
theorem copyEdge_fixed_shape {mountain : Mountain} {source : Ref}
    {sourceCell : Cell} {parent : Ref} {shift rootColumn : Nat}
    (hSource : lookup mountain source = .ok sourceCell)
    (hNonzero : sourceCell.row ≠ 0) (hLeft : sourceCell.left = some parent)
    (hFixed : parent.column < rootColumn)
    (hDestination : parent.column < source.column + shift) (target : Row) :
    copyEdge mountain source shift rootColumn target = .ok ⟨target, 0, some parent⟩ := by
  simp [copyEdge, hSource, hNonzero, leftOf, hLeft, hFixed, hDestination]

/-- An executed contour edge crossing the lift cap has the exact canonical
B row with its fixed, actually readable father. The initial target is the
effective lower row; it need not be the physical marker's unlifted row. -/
theorem contour_fixed_exit_edge {mountain : Mountain}
    {sourceColumn shift rootColumn index : Nat} {markerIndices : List Nat}
    {current upper parentCell : Cell} {parent : Ref} {rest result : List Cell}
    {root target : Row} {scale : Nat}
    (hSource : lookup mountain ⟨sourceColumn, index + 1⟩ = .ok upper)
    (hLeft : upper.left = some parent)
    (hParent : lookup mountain parent = .ok parentCell)
    (hFixed : parent.column < rootColumn)
    (hDestination : parent.column < sourceColumn + shift)
    (hOldB : upper.row = Row.B current.row parentCell.row)
    (hTargetLower : root ≤ target) (hTargetCap : target < Row.bump root scale)
    (hCurrentLower : root ≤ current.row) (hCurrentCap : current.row < Row.bump root scale)
    (hParentRoot : parentCell.row ≤ root) (hExit : Row.bump root scale ≤ upper.row)
    (hContinue : ¬ (current.value = 1 ∨ index + 1 ∈ markerIndices))
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index
      (Row.lift root target current.row) current (upper :: rest) = .ok result) :
    ∃ copied tail, result = copied :: tail ∧ copied.left = some parent ∧
      lookup mountain parent = .ok parentCell ∧
      copied.row = Row.B (Row.lift root target current.row) parentCell.row ∧
      parentCell.row ≤ Row.lift root target current.row ∧
      copied.row = upper.row ∧
      contour mountain sourceColumn markerIndices shift rootColumn (index + 1)
        copied.row upper rest = .ok tail := by
  have hRows : current.row < upper.row := by rw [hOldB]; exact Row.lt_B _ _
  have hNonzero : upper.row ≠ 0 := ne_of_gt ((Row.zero_le current.row).trans_lt hRows)
  let next := Row.bump (Row.lift root target current.row) (Row.jump current.row upper.row - 1)
  have hNextLift : next = Row.lift root target upper.row := by
    dsimp only [next]
    rw [hOldB, Row.B, Row.jump_bump, Nat.add_sub_cancel, Row.lift_bump hCurrentLower]
  have hNextB : next = Row.B (Row.lift root target current.row) parentCell.row := by
    rw [hNextLift, hOldB]
    exact Row.lift_B_fixed_parent hTargetLower hTargetCap hCurrentLower hCurrentCap
      hParentRoot (by simpa only [← hOldB] using hExit)
  have hNextOld : next = upper.row :=
    hNextLift.trans (Row.lift_eq_of_ge_cap hTargetLower hTargetCap hExit)
  have hCopy := copyEdge_fixed_shape hSource hNonzero hLeft hFixed hDestination next
  cases hTail : contour mountain sourceColumn markerIndices shift rootColumn
      (index + 1) next upper rest with
  | error error =>
    dsimp only [next] at hCopy hTail
    simp [contour, hContinue, hRows, hCopy, hTail] at hRun
  | ok tail =>
    have hResult : (⟨next, 0, some parent⟩ : Cell) :: tail = result := by
      dsimp only [next] at hCopy hTail
      simpa [contour, hContinue, hRows, hCopy, hTail] using hRun
    refine ⟨⟨next, 0, some parent⟩, tail, hResult.symm, rfl, hParent,
      hNextB, ?_, hNextOld, hTail⟩
    exact hParentRoot.trans (hCurrentLower.trans
      (Row.lift_ge_source hTargetLower hCurrentLower))

/-- An actual canonical source build supplies the old B rule. The ambient
copying mountain only preserves those old columns; its new columns need not
be Normal or satisfy MountainSteps. The current and upper are actual adjacent
source reads, and the retained father is read in the original build. -/
theorem contour_fixed_exit_edge_of_build {values : List Nat} {before mountain : Mountain}
    (hBuild : Canonical.build values = .ok before) (hPreserved : PreservesColumns before mountain)
    {sourceColumn shift rootColumn index : Nat} {nodes : Column}
    (hColumn : before[sourceColumn]? = some nodes)
    {current upper parentCell : Cell} {parent : Ref}
    (hCurrent : nodes[index]? = some current) (hUpper : nodes[index + 1]? = some upper)
    (hIndex : 0 < index) (hLeft : upper.left = some parent)
    (hParent : Canonical.cellAt before parent = .ok parentCell)
    {markerIndices : List Nat} {rest result : List Cell} {root target : Row} {scale : Nat}
    (hFixed : parent.column < rootColumn)
    (hTargetLower : root ≤ target) (hTargetCap : target < Row.bump root scale)
    (hCurrentLower : root ≤ current.row) (hCurrentCap : current.row < Row.bump root scale)
    (hParentRoot : parentCell.row ≤ root) (hExit : Row.bump root scale ≤ upper.row)
    (hContinue : ¬ (current.value = 1 ∨ index + 1 ∈ markerIndices))
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index
      (Row.lift root target current.row) current (upper :: rest) = .ok result) :
    ∃ copied tail, result = copied :: tail ∧ copied.left = some parent ∧
      lookup mountain parent = .ok parentCell ∧
      copied.row = Row.B (Row.lift root target current.row) parentCell.row ∧
      parentCell.row ≤ Row.lift root target current.row ∧
      copied.row = upper.row ∧
      contour mountain sourceColumn markerIndices shift rootColumn (index + 1)
        copied.row upper rest = .ok tail := by
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
  have hSteps : ColumnSteps before sourceColumn nodes :=
    hNodes ▸ build_steps hBuild sourceColumn hc
  obtain ⟨_, oldParent, oldParentCell, hParentColumn, _, hOldParent, hOldB, _, hOldLeft⟩ :=
    hSteps index current upper hCurrent hUpper hIndex
  have hParentEq : oldParent = parent := Option.some.inj (hOldLeft.symm.trans hLeft)
  subst oldParent
  have hCellEq : oldParentCell = parentCell := Except.ok.inj (hOldParent.symm.trans hParent)
  subst oldParentCell
  have hSourceRead : lookup mountain ⟨sourceColumn, index + 1⟩ = .ok upper :=
    (hPreserved.lookup hc).trans (lookup_ok_iff.mpr ⟨nodes, hColumn, hUpper⟩)
  have hParentRead : lookup mountain parent = .ok parentCell :=
    (hPreserved.lookup (hParentColumn.trans hc)).trans (lookup_ok_iff.mpr (cellAt_ok_iff.mp hParent))
  exact contour_fixed_exit_edge hSourceRead hLeft hParentRead hFixed
    (by omega) hOldB hTargetLower hTargetCap hCurrentLower hCurrentCap hParentRoot
    hExit hContinue hRun

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copyEdge_fixed_shape
#print axioms OmegaY.Expansion.contour_fixed_exit_edge
#print axioms OmegaY.Expansion.contour_fixed_exit_edge_of_build
