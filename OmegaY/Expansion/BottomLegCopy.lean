/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BottomLegCopy.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ColumnCopyData
import OmegaY.Expansion.FinishSupport
import OmegaY.Expansion.PreparedPhantom
import OmegaY.Canonical.BottomLegs

/-! Exact preservation of bottom left legs by the actual column copier.
The source bottom points to the preceding phantom. Its translated copy
does too, whether the bottom is a marker or the first phantom-contour step.
Sorting and numerical backfill preserve that same candidate's row and left
reference, and strict output row order identifies its returned index as one.
No output normality or bottom-leg invariant is assumed. -/

namespace OmegaY.Expansion

open Canonical

theorem copyEdge_bottom_exact {mountain : Mountain} (hValid : MountainValid mountain)
    {source : Ref} {bottom : Cell} (hSource : lookup mountain source = .ok bottom)
    (hRow : bottom.row = 1) (hLeft : bottom.left = some ⟨source.column - 1, 0⟩)
    {shift rootColumn : Nat} (hRoot : rootColumn < source.column)
    (hDestination : source.column + shift ≤ mountain.size) :
    copyEdge mountain source shift rootColumn 1 =
      .ok ⟨1, 0, some ⟨source.column + shift - 1, 0⟩⟩ := by
  have hFixed : ¬ source.column - 1 < rootColumn := by omega
  have hc : source.column - 1 + shift < mountain.size := by omega
  have hBelow := below_one hValid hc
  have hNot : ¬ source.column + shift ≤ source.column - 1 + shift := by omega
  have hColumn : source.column - 1 + shift = source.column + shift - 1 := by omega
  have hRun : copyEdge mountain source shift rootColumn 1 =
      .ok ⟨1, 0, some ⟨source.column - 1 + shift, 0⟩⟩ := by
    simp [copyEdge, hSource, hRow, leftOf, hLeft, hFixed, hBelow, hNot,
      ne_of_gt Row.zero_lt_one]
  simpa only [hColumn] using hRun

/-- If index one is not marked, the actual phantom contour begins with
the exact translated bottom candidate. The tail need only have succeeded. -/
theorem contour_phantom_bottom_exact {mountain : Mountain} (hValid : MountainValid mountain)
    {sourceColumn shift rootColumn : Nat} {sources : Column}
    (hSources : mountain[sourceColumn]? = some sources)
    {bottom : Cell} (hBottom : sources[1]? = some bottom)
    (hBottomLeft : bottom.left = some ⟨sourceColumn - 1, 0⟩)
    (hRoot : rootColumn < sourceColumn)
    (hDestination : sourceColumn + shift ≤ mountain.size)
    (markerIndices : List Nat) (hNotMarked : 1 ∉ markerIndices)
    {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn 0 0 phantom
      (sources.toList.drop 1) = .ok result) :
    ∃ tail, result = ⟨1, 0, some ⟨sourceColumn + shift - 1, 0⟩⟩ :: tail := by
  obtain ⟨hc, hSourcesEq⟩ := Array.getElem?_eq_some_iff.mp hSources
  have hCV : ColumnValid mountain sourceColumn sources := hSourcesEq ▸ hValid sourceColumn hc
  have hBottomRow := hCV.bottom_row bottom hBottom
  have hb : 1 < sources.size := (Array.getElem?_eq_some_iff.mp hBottom).1
  have hRest : sources.toList.drop 1 = bottom :: sources.toList.drop 2 := by
    have hh := List.drop_eq_getElem_cons (l := sources.toList) (i := 1) (by simpa using hb)
    have he : sources[1] = bottom := (Array.getElem?_eq_some_iff.mp hBottom).2
    simpa only [Array.getElem_toList, he] using hh
  have hStep : Row.bump (0 : Row) (Row.jump 0 1 - 1) = 1 := by
    rw [← zero_bump_zero, Row.jump_bump]
  have hRead : lookup mountain ⟨sourceColumn, 1⟩ = .ok bottom :=
    lookup_ok_iff.mpr ⟨sources, hSources, hBottom⟩
  have hCopy := copyEdge_bottom_exact hValid hRead hBottomRow hBottomLeft hRoot hDestination
  cases hTail : contour mountain sourceColumn markerIndices shift rootColumn 1 1 bottom
      (sources.toList.drop 2) with
  | error e =>
      simp [hRest, contour, phantom, hNotMarked, hBottomRow, hStep, hCopy, hTail,
        not_le_of_gt Row.zero_lt_one] at hRun
  | ok tail =>
      refine ⟨tail, ?_⟩
      simpa [hRest, contour, phantom, hNotMarked, hBottomRow, hStep, hCopy, hTail,
        not_le_of_gt Row.zero_lt_one] using hRun.symm

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- One concrete candidate has both the bottom row and its exact previous
phantom endpoint. This is stronger than independent row/endpoint membership. -/
theorem candidates_bottom_exact {bottom : Cell} (hBottom : d.sources[1]? = some bottom)
    (hBottomLeft : bottom.left = some ⟨sourceColumn - 1, 0⟩)
    (hRoot : rootColumn < sourceColumn) :
    (⟨1, 0, some ⟨mountain.size - 1, 0⟩⟩ : Cell) ∈ d.candidates := by
  let bottomRef : Ref := ⟨sourceColumn, 1⟩
  have hBottomRow := d.source_valid.bottom_row bottom hBottom
  have hRead : lookup mountain bottomRef = .ok bottom :=
    lookup_ok_iff.mpr ⟨d.sources, d.source_column, hBottom⟩
  have hExact := copyEdge_bottom_exact d.ambient_valid hRead hBottomRow hBottomLeft hRoot d.destination.le
  rw [d.destination] at hExact
  by_cases hBottomMarker : bottomRef ∈ d.bucket
  · let s := d.marker_data bottomRef hBottomMarker
    have hCurrent : s.current = bottom := Option.some.inj (s.current_at.symm.trans hBottom)
    obtain ⟨copied, path, gap, hResult, hCopy, _, _, _, _, _, _, _⟩ :=
      copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
        d.source_top references _ s.current_at s.upper_at s.upper_left s.parent_nodes s.target_at
        s.reference s.target_lower (d.segment_run hBottomMarker)
    rw [hCurrent, hBottomRow] at hCopy
    have hCopied : copied = ⟨1, 0, some ⟨mountain.size - 1, 0⟩⟩ :=
      Except.ok.inj (hCopy.symm.trans hExact)
    exact List.mem_flatMap.mpr ⟨bottomRef, hBottomMarker, by rw [hResult, hCopied]; simp⟩
  · have hNotMarked : 1 ∉ d.bucket.map Ref.index := by
      intro h
      obtain ⟨entry, hm, hIndex⟩ := List.mem_map.mp h
      have hColumn := d.marker_columns entry hm
      have he : entry = bottomRef := by
        cases entry
        simp_all only [bottomRef]
      exact hBottomMarker (he ▸ hm)
    let marker : Ref := ⟨sourceColumn, 0⟩
    have hm : marker ∈ d.bucket := d.phantom_marker
    let s := d.marker_data marker hm
    have hCurrent : s.current = phantom :=
      Option.some.inj (s.current_at.symm.trans d.source_valid.phantom)
    have hZero : s.targetCell.row = 0 := d.target_zero hm (congrArg Cell.row hCurrent)
    obtain ⟨copied, path, gap, hResult, _, _, _, hContour, _, _, _, _⟩ :=
      copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero d.destination.le
        d.source_top references _ s.current_at s.upper_at s.upper_left s.parent_nodes s.target_at
        s.reference s.target_lower (d.segment_run hm)
    rw [hCurrent, hZero] at hContour
    obtain ⟨tail, hPath⟩ := contour_phantom_bottom_exact d.ambient_valid d.source_column hBottom
      hBottomLeft hRoot d.destination.le _ hNotMarked hContour
    rw [d.destination] at hPath
    exact List.mem_flatMap.mpr ⟨marker, hm, by rw [hResult, hPath]; simp⟩

/-- Actual sorting/backfill places the certified bottom candidate at index
one and preserves its concrete stored reference. Output validity is derived
from the input-only `ColumnCopyData` record. -/
theorem copyColumn_bottom_left {bottom : Cell} (hBottom : d.sources[1]? = some bottom)
    (hBottomLeft : bottom.left = some ⟨sourceColumn - 1, 0⟩)
    (hRoot : rootColumn < sourceColumn) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column) :
    ∃ copiedBottom, column[1]? = some copiedBottom ∧
      copiedBottom.left = some ⟨mountain.size - 1, 0⟩ := by
  obtain ⟨certified, hCertified, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : certified = column := Except.ok.inj (hCertified.symm.trans hRun)
  subst certified
  have hFinish : finish mountain d.candidates = .ok column := d.copyColumn_eq_finish.symm.trans hRun
  obtain ⟨index, cell, hCell, hShape⟩ :=
    finish_candidate_read hFinish (d.candidates_bottom_exact hBottom hBottomLeft hRoot)
  have hRow : cell.row = 1 := hShape.1.symm
  have hb : 1 < column.size := by have hSize := hValid.size_ge_two; omega
  have hOutput : column[1]? = some column[1] := Array.getElem?_eq_getElem hb
  have hOutputRow := hValid.bottom_row _ hOutput
  have hIndex : index = 1 := by
    rcases lt_trichotomy index 1 with hLt | hEq | hGt
    · have hh := hValid.rows_strict _ _ _ _ hCell hOutput hLt
      rw [hRow, hOutputRow] at hh
      exact False.elim (lt_irrefl _ hh)
    · exact hEq
    · have hh := hValid.rows_strict _ _ _ _ hOutput hCell hGt
      rw [hRow, hOutputRow] at hh
      exact False.elim (lt_irrefl _ hh)
  exact ⟨cell, hIndex ▸ hCell, hShape.2.symm⟩

/-- A source column frozen from any mountain with certified bottom legs
supplies the exact input endpoint. The enlarged ambient need not be a
canonical build, and its unrelated columns need no bottom-leg hypothesis. -/
theorem copyColumn_bottom_left_of_source_legs {base : Mountain}
    (hBaseLegs : BottomLegs base) (hSourceBase : base[sourceColumn]? = some d.sources)
    (hRoot : rootColumn < sourceColumn) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column) :
    ∃ copiedBottom, column[1]? = some copiedBottom ∧
      copiedBottom.left = some ⟨mountain.size - 1, 0⟩ := by
  obtain ⟨hc, hSourceEq⟩ := Array.getElem?_eq_some_iff.mp hSourceBase
  obtain ⟨bottom, hBottom, hLeft⟩ := hBaseLegs sourceColumn hc
  rw [hSourceEq] at hBottom
  rw [if_neg (Nat.ne_of_gt d.source_nonzero)] at hLeft
  exact d.copyColumn_bottom_left hBottom hLeft hRoot hRun

/-- In particular the successful old canonical build supplies the source
bottom leg, even during a later block with an arbitrary valid ambient. -/
theorem copyColumn_bottom_left_of_build {base : Mountain} {values : List Nat}
    (hBuild : Canonical.build values = .ok base)
    (hSourceBase : base[sourceColumn]? = some d.sources)
    (hRoot : rootColumn < sourceColumn) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column) :
    ∃ copiedBottom, column[1]? = some copiedBottom ∧
      copiedBottom.left = some ⟨mountain.size - 1, 0⟩ :=
  d.copyColumn_bottom_left_of_source_legs (build_bottom_legs hBuild) hSourceBase hRoot hRun

end ColumnCopyData

end OmegaY.Expansion

#print axioms OmegaY.Expansion.copyEdge_bottom_exact
#print axioms OmegaY.Expansion.contour_phantom_bottom_exact
#print axioms OmegaY.Expansion.ColumnCopyData.candidates_bottom_exact
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_bottom_left
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_bottom_left_of_build
