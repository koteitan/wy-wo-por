/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SegmentLegs.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialCandidateLegs

/-! Full-segment leg validity from local source geometry. The ambient
mountain may contain copied columns; only the source column requires power
steps, and no new output is assumed valid or canonical. -/

namespace OmegaY.Expansion

open Canonical

theorem copySegment_legs_of_source {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn index : Nat} {sources : Column}
    (hSources : mountain[sourceColumn]? = some sources)
    (hSourcePositive : 0 < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size) (hTop : TopOne sources)
    (hPower : ColumnPowerSteps sources) (references : List Ref) (markerIndices : List Nat)
    {current upper : Cell} (hCurrent : sources[index]? = some current)
    (hUpper : sources[index + 1]? = some upper) {sourceParent : Ref}
    (hLeft : upper.left = some sourceParent) {parentNodes : Column}
    (hParentNodes : mountain[sourceParent.column + shift]? = some parentNodes)
    {targetIndex : Nat} {targetCell : Cell}
    (hTarget : parentNodes[targetIndex]? = some targetCell)
    (hReference : referenceAt mountain references current.row = .ok targetCell.row)
    (hLow : current.row ≤ targetCell.row) {result : List Cell}
    (hRun : copySegment mountain sources references sourceColumn markerIndices
      shift rootColumn index = .ok result) :
    ∀ cell ∈ result, CellLegs mountain (sourceColumn + shift) cell := by
  obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hSourceValid : ColumnValid mountain sourceColumn sources := hNodes ▸ hValid sourceColumn hc
  obtain ⟨copied, upperPath, gap, hResult, hCopy, _, _, hContour, hFill, _, _, _⟩ :=
    copySegment_result_decomposition hValid hSources hSourcePositive hDestination hTop
      references markerIndices hCurrent hUpper hLeft hParentNodes hTarget hReference hLow hRun
  have hCurrentRead : lookup mountain ⟨sourceColumn, index⟩ = .ok current :=
    lookup_ok_iff.mpr ⟨sources, hSources, hCurrent⟩
  have hCopiedLegs := copyEdge_same_row_legs hValid hCurrentRead hSourcePositive hDestination hCopy
  have hContourParents := contour_parent_rows_of_success hValid hSources hSourcePositive
    hDestination hPower markerIndices targetCell.row hCurrent rfl hLow hContour
  have hUpperRead : lookup mountain ⟨sourceColumn, index + 1⟩ = .ok upper :=
    lookup_ok_iff.mpr ⟨sources, hSources, hUpper⟩
  obtain ⟨hp, hParents⟩ := Array.getElem?_eq_some_iff.mp hParentNodes
  have hParentValid : ColumnValid mountain (sourceParent.column + shift) parentNodes :=
    hParents ▸ hValid _ hp
  have hParentLeft : sourceParent.column < sourceColumn :=
    (hSourceValid.stored_valid _ _ _ hUpper hLeft).1
  obtain ⟨certifiedGap, hCertified, _, _, hGapParents⟩ :=
    fill_spec_of_valid_column hUpperRead hLeft hParentNodes hParentValid hTarget hParentLeft
      (low := current.row)
  have hGapEq : certifiedGap = gap := Except.ok.inj (hCertified.symm.trans hFill)
  rw [hGapEq] at hGapParents
  intro cell hCell
  rw [hResult] at hCell
  rcases List.mem_append.mp hCell with hFirst | hGapMem
  · rcases List.mem_append.mp hFirst with hCopyMem | hContourMem
    · have he : cell = copied := List.mem_singleton.mp hCopyMem
      exact he ▸ hCopiedLegs
    · obtain ⟨parent, parentCell, hCopiedLeft, hRead, hColumn, hRow⟩ :=
        hContourParents cell hContourMem
      exact CellLegs.of_parent hCopiedLeft hRead hColumn hRow
  · obtain ⟨_, _, _, parent, parentCell, hCopiedLeft, hRead, hColumn, hRow⟩ :=
      hGapParents cell hGapMem
    exact CellLegs.of_parent hCopiedLeft hRead hColumn hRow.le

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copySegment_legs_of_source
