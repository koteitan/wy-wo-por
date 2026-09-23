/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SegmentPower.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FillPathActual
import OmegaY.Expansion.FinishPowerSteps
import OmegaY.Expansion.SegmentBounds

/-! A whole actual marker segment, in ascending row order, is the marker,
the actual continuous reference-fill path, and its actual contour. Their
shared endpoint is the selected target, including equal low/high endpoints.
The original executable order remains unchanged. -/

namespace OmegaY.Expansion

open Canonical

private theorem getLast?_join_at {start target : Row} {before after : List Row}
    (hLast : (start :: before).getLast? = some target) :
    (start :: (before ++ after)).getLast? = (target :: after).getLast? := by
  cases after with
  | nil => simpa only [List.append_nil, List.getLast?_singleton] using hLast
  | cons head tail =>
    change ((start :: before) ++ head :: tail).getLast? = _
    rw [List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_cons_cons]

/-- All four conclusions concern the real sorting expression on the actual
helper result. Source top conditions supply contour success; only the
already available parent column needs the power law for reference filling. -/
theorem copySegment_sorted_power {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn index : Nat} {sources : Column}
    (hSources : mountain[sourceColumn]? = some sources) (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne sources)
    (references : List Ref) (markerIndices : List Nat)
    {current upper : Cell} (hCurrent : sources[index]? = some current)
    (hUpper : sources[index + 1]? = some upper) {sourceParent : Ref}
    (hLeft : upper.left = some sourceParent) {parentNodes : Column}
    (hParentNodes : mountain[sourceParent.column + shift]? = some parentNodes)
    {targetIndex : Nat} {targetCell : Cell} (hTarget : parentNodes[targetIndex]? = some targetCell)
    (hReference : referenceAt mountain references current.row = .ok targetCell.row)
    (hLow : current.row ≤ targetCell.row) (hParentPower : ColumnPowerSteps parentNodes)
    {lowIndex : Nat} {lowCell : Cell} (hParentLow : parentNodes[lowIndex]? = some lowCell)
    (hParentLowRow : lowCell.row = current.row) {result : List Cell}
    (hRun : copySegment mountain sources references sourceColumn markerIndices shift rootColumn index =
      .ok result) :
    RowsPowerSteps ((finishSort result).map Cell.row) ∧
      ((finishSort result).map Cell.row).head? = some current.row ∧
      ((finishSort result).map Cell.row).getLast? =
        some (Row.run targetCell.row (contourExponents markerIndices index current
          (sources.toList.drop (index + 1)))) ∧
      targetCell.row ∈ (finishSort result).map Cell.row := by
  obtain ⟨copied, path, gap, hResult, _, hCopiedRow, _, hContour, hFill, _, _, _⟩ :=
    copySegment_result_decomposition hValid hSources hSourcePositive hDestination hTop
      references markerIndices hCurrent hUpper hLeft hParentNodes hTarget hReference hLow hRun
  obtain ⟨hs, hSourceEq⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hSourceValid : ColumnValid mountain sourceColumn sources := hSourceEq ▸ hValid _ hs
  obtain ⟨hp, hParentEq⟩ := Array.getElem?_eq_some_iff.mp hParentNodes
  have hParentValid : ColumnValid mountain (sourceParent.column + shift) parentNodes :=
    hParentEq ▸ hValid _ hp
  have hUpperRead : lookup mountain ⟨sourceColumn, index + 1⟩ = .ok upper :=
    lookup_ok_iff.mpr ⟨sources, hSources, hUpper⟩
  have hLeftward := (hSourceValid.stored_valid _ _ _ hUpper hLeft).1
  obtain ⟨otherGap, hOtherGap, hGapCells, _, _⟩ :=
    fill_spec_of_valid_column hUpperRead hLeft hParentNodes hParentValid hTarget hLeftward
      (low := current.row)
  have hGapEq : otherGap = gap := Except.ok.inj (hOtherGap.symm.trans hFill)
  rw [hGapEq] at hGapCells
  let gapRows := fillCellsAscendingRows parentNodes (sourceParent.column + shift)
    current.row targetCell.row
  have hGapFacts : RowsPowerSteps (current.row :: gapRows) ∧
      (current.row :: gapRows).getLast? = some targetCell.row := by
    have h := fillCellsAscendingRows_power_steps (fillRowsStrict_of_columnValid hParentValid)
      hParentPower hParentLow hTarget (by simpa only [hParentLowRow] using hLow)
      (column := sourceParent.column + shift)
    simpa only [hParentLowRow] using h
  have hGapPerm : gapRows.Perm (gap.map Cell.row) := by
    rw [hGapCells]
    exact fillCellsAscendingRows_perm _ _ _ _
  have hPathPower := contour_power_steps_of_success hValid hSources hSourcePositive
    hDestination hTop markerIndices targetCell.row hCurrent rfl hContour
  let ascending := current.row :: (gapRows ++ path.map Cell.row)
  have hPower : RowsPowerSteps ascending :=
    RowsPowerSteps.append_at hGapFacts.1 hGapFacts.2 hPathPower
  have hPerm : ascending.Perm (result.map Cell.row) := by
    rw [hResult]
    simp only [List.map_append, List.map_cons, hCopiedRow,
      List.cons_append]
    exact List.Perm.cons _ ((hGapPerm.append_right _).trans List.perm_append_comm)
  have hSort : (finishSort result).map Cell.row = ascending :=
    finishSort_rows_eq_of_power_perm hPerm hPower
  rw [hSort]
  refine ⟨hPower, rfl, ?_, ?_⟩
  · change (current.row :: (gapRows ++ path.map Cell.row)).getLast? = _
    rw [getLast?_join_at hGapFacts.2]
    obtain ⟨otherPath, hOtherPath, hTrace, _⟩ := contour_total hValid hSources hSourcePositive
      hDestination hTop markerIndices targetCell.row hCurrent rfl (rootColumn := rootColumn)
    have he : otherPath = path := Except.ok.inj (hOtherPath.symm.trans hContour)
    subst otherPath
    rw [hTrace]
    exact bumpTrace_last targetCell.row _
  · have hMember : targetCell.row ∈ current.row :: gapRows := by
      exact List.mem_of_getLast? hGapFacts.2
    exact List.mem_append_left (path.map Cell.row) hMember

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copySegment_sorted_power
