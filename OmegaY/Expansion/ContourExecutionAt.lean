/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ContourExecutionAt.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.AdjacentCanonicalCases

/-!
# Indexed provenance of actual contour execution

Successful output reads recover the precise source suffix, each executed
copyEdge call, and the unchanged common lift root and target. No output row
equation or source-pair/copy-success witness is supplied as a premise.
-/

namespace OmegaY.Expansion

open Canonical

private theorem copied_requested_row {mountain : Mountain} {source : Ref}
    {shift rootColumn : Nat} {row : Row} {copied : Cell}
    (hRun : copyEdge mountain source shift rootColumn row = .ok copied) : copied.row = row := by
  cases hSource : lookup mountain source with
  | error error => simp [copyEdge, hSource] at hRun
  | ok sourceCell =>
    by_cases hZero : sourceCell.row = 0
    · have he : (⟨row, 0, none⟩ : Cell) = copied := by
        simpa [copyEdge, hSource, hZero] using hRun
      exact congrArg Cell.row he.symm
    · cases hLeft : leftOf sourceCell with
      | error error => simp [copyEdge, hSource, hZero, hLeft] at hRun
      | ok oldParent =>
        by_cases hFixed : oldParent.column < rootColumn
        · by_cases hDestination : oldParent.column < source.column + shift
          · have he : (⟨row, 0, some oldParent⟩ : Cell) = copied := by
              simpa [copyEdge, hSource, hZero, hLeft, hFixed,
                Nat.not_le_of_gt hDestination] using hRun
            exact congrArg Cell.row he.symm
          · simp [copyEdge, hSource, hZero, hLeft, hFixed,
              Nat.le_of_not_gt hDestination] at hRun
        · cases hBelow : below mountain (oldParent.column + shift) row with
          | error error => simp [copyEdge, hSource, hZero, hLeft, hFixed, hBelow] at hRun
          | ok parent =>
            by_cases hDestination : parent.column < source.column + shift
            · have he : (⟨row, 0, some parent⟩ : Cell) = copied := by
                simpa [copyEdge, hSource, hZero, hLeft, hFixed, hBelow,
                  Nat.not_le_of_gt hDestination] using hRun
              exact congrArg Cell.row he.symm
            · simp [copyEdge, hSource, hZero, hLeft, hFixed, hBelow,
                Nat.le_of_not_gt hDestination] at hRun

private theorem execution_suffix_cons {nodes : Column} {index : Nat} {upper : Cell}
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = upper :: rest) :
    nodes[index + 1]? = some upper ∧ nodes.toList.drop ((index + 1) + 1) = rest := by
  constructor
  · simpa only [List.head?_drop, Array.getElem?_toList, List.head?_cons]
      using congrArg List.head? hRest
  · simpa only [List.tail_drop, List.tail_cons] using congrArg List.tail hRest

/-- A witness for the exact source step producing output position k. The
suffix execution is retained at its actual recursively advanced arguments. -/
structure ContourNthExecution (mountain : Mountain) (sourceColumn : Nat)
    (markerIndices : List Nat) (shift rootColumn : Nat) (nodes : Column)
    (root target : Row) (startIndex : Nat) (result : List Cell) (position : Nat)
    (copied : Cell) where
  lower : Cell
  upper : Cell
  tail : List Cell
  lower_at : nodes[startIndex + position]? = some lower
  upper_at : nodes[startIndex + position + 1]? = some upper
  root_lower : root ≤ lower.row
  source_rows : lower.row < upper.row
  lower_not_one : lower.value ≠ 1
  upper_nonzero : upper.row ≠ 0
  no_markers : ∀ middle, startIndex < middle → middle ≤ startIndex + position + 1 →
    middle ∉ markerIndices
  copy_run : copyEdge mountain ⟨sourceColumn, startIndex + position + 1⟩ shift rootColumn
    (Row.lift root target upper.row) = .ok copied
  suffix_run : contour mountain sourceColumn markerIndices shift rootColumn
    (startIndex + position + 1) (Row.lift root target upper.row) upper
    (nodes.toList.drop (startIndex + position + 2)) = .ok tail
  result_drop : result.drop (position + 1) = tail
  copied_row : copied.row = Row.lift root target upper.row

/-- The two concrete source reads and every intermediate continuation test
come from the real run. Premature-one and marked-index stops are ruled out
by the existence of this output position, not by an extra assumption. -/
theorem contour_execution_at {mountain : Mountain} {sourceColumn shift rootColumn : Nat}
    {nodes : Column} (hPower : ColumnPowerSteps nodes) (markerIndices : List Nat)
    {root target : Row} {index : Nat} {current : Cell}
    (hCurrent : nodes[index]? = some current) (hRoot : root ≤ current.row)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest)
    {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index
      (Row.lift root target current.row) current rest = .ok result)
    {position : Nat} {copied : Cell} (hCopied : result[position]? = some copied) :
    Nonempty (ContourNthExecution mountain sourceColumn markerIndices shift rootColumn nodes
      root target index result position copied) := by
  induction position generalizing index current rest result with
  | zero | succ position ih =>
    cases rest with
    | nil =>
      by_cases hOne : current.value = 1
      · have he : result = [] := by simpa [contour, hOne] using hRun.symm
        simp [he] at hCopied
      · simp [contour, hOne] at hRun
    | cons upper rest =>
      by_cases hStop : current.value = 1 ∨ index + 1 ∈ markerIndices
      · have he : result = [] := by simpa [contour, hStop] using hRun.symm
        simp [he] at hCopied
      · by_cases hRows : current.row < upper.row
        · obtain ⟨hUpper, hTail⟩ := execution_suffix_cons hRest
          have hNextLift : Row.bump (Row.lift root target current.row)
              (Row.jump current.row upper.row - 1) = Row.lift root target upper.row := by
            rw [← Row.lift_bump hRoot]
            exact congrArg (Row.lift root target) (hPower index current upper hCurrent hUpper).symm
          cases hCopy : copyEdge mountain ⟨sourceColumn, index + 1⟩ shift rootColumn
              (Row.lift root target upper.row) with
          | error error => simp [contour, hStop, hRows, hNextLift, hCopy] at hRun
          | ok first =>
            cases hRemaining : contour mountain sourceColumn markerIndices shift rootColumn
                (index + 1) (Row.lift root target upper.row) upper rest with
            | error error => simp [contour, hStop, hRows, hNextLift, hCopy, hRemaining] at hRun
            | ok remaining =>
              have hResult : first :: remaining = result := by
                simpa [contour, hStop, hRows, hNextLift, hCopy, hRemaining] using hRun
              subst result
              first
              | have he : first = copied := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using hCopied
                subst first
                exact ⟨{
                  lower := current
                  upper := upper
                  tail := remaining
                  lower_at := by simpa only [Nat.add_zero] using hCurrent
                  upper_at := by simpa only [Nat.add_zero] using hUpper
                  root_lower := hRoot
                  source_rows := hRows
                  lower_not_one := (not_or.mp hStop).1
                  upper_nonzero := ne_of_gt ((Row.zero_le current.row).trans_lt hRows)
                  no_markers := by
                    intro middle hLow hHigh
                    have he : middle = index + 1 := by omega
                    exact he ▸ (not_or.mp hStop).2
                  copy_run := by simpa only [Nat.add_zero] using hCopy
                  suffix_run := by
                    simpa only [Nat.add_zero, show index + 2 = (index + 1) + 1 by omega, hTail]
                      using hRemaining
                  result_drop := by simp
                  copied_row := copied_requested_row hCopy }⟩
              | obtain ⟨next⟩ := ih hUpper (hRoot.trans hRows.le) hTail hRemaining
                    (by simpa only [List.getElem?_cons_succ] using hCopied)
                exact ⟨{
                  lower := next.lower
                  upper := next.upper
                  tail := next.tail
                  lower_at := by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next.lower_at
                  upper_at := by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next.upper_at
                  root_lower := next.root_lower
                  source_rows := next.source_rows
                  lower_not_one := next.lower_not_one
                  upper_nonzero := next.upper_nonzero
                  no_markers := by
                    intro middle hLow hHigh
                    by_cases he : middle = index + 1
                    · exact he ▸ (not_or.mp hStop).2
                    · exact next.no_markers middle (by omega) (by omega)
                  copy_run := by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next.copy_run
                  suffix_run := by simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using next.suffix_run
                  result_drop := by simpa only [List.drop_succ_cons] using next.result_drop
                  copied_row := next.copied_row }⟩
        · simp [contour, hStop, hRows] at hRun

 /-- A consecutive pair in the returned path comes from consecutive actual
source indices. Both copy calls retain the same lift root and target. -/
structure ContourAdjacentExecution (mountain : Mountain) (sourceColumn : Nat)
    (markerIndices : List Nat) (shift rootColumn : Nat) (nodes : Column)
    (root target : Row) (startIndex : Nat) (result : List Cell) (position : Nat)
    (copiedLower copiedUpper : Cell) where
  lower : Cell
  upper : Cell
  tail : List Cell
  lower_at : nodes[startIndex + position + 1]? = some lower
  upper_at : nodes[startIndex + position + 2]? = some upper
  root_lower : root ≤ lower.row
  source_rows : lower.row < upper.row
  lower_not_one : lower.value ≠ 1
  lower_nonzero : lower.row ≠ 0
  upper_nonzero : upper.row ≠ 0
  no_markers : ∀ middle, startIndex < middle → middle ≤ startIndex + position + 2 →
    middle ∉ markerIndices
  lower_copy : copyEdge mountain ⟨sourceColumn, startIndex + position + 1⟩ shift rootColumn
    (Row.lift root target lower.row) = .ok copiedLower
  upper_copy : copyEdge mountain ⟨sourceColumn, startIndex + position + 2⟩ shift rootColumn
    (Row.lift root target upper.row) = .ok copiedUpper
  suffix_run : contour mountain sourceColumn markerIndices shift rootColumn
    (startIndex + position + 2) (Row.lift root target upper.row) upper
    (nodes.toList.drop (startIndex + position + 3)) = .ok tail
  result_drop : result.drop (position + 2) = tail
  lower_row : copiedLower.row = Row.lift root target lower.row
  upper_row : copiedUpper.row = Row.lift root target upper.row

section SourceReads

variable {mountain : Mountain} {sourceColumn : Nat} {markerIndices : List Nat}
  {shift rootColumn : Nat} {nodes : Column} {root target : Row}
  {startIndex : Nat} {result : List Cell} {position : Nat} {copiedLower copiedUpper : Cell}
  (execution : ContourAdjacentExecution mountain sourceColumn markerIndices shift rootColumn nodes
    root target startIndex result position copiedLower copiedUpper)

/-- The source may be read in the original frozen build or in an ambient
mountain preserving its complete column. The column read is explicit. -/
theorem ContourAdjacentExecution.lower_cellAt {sourceMountain : Mountain}
    (hColumn : sourceMountain[sourceColumn]? = some nodes) :
    Canonical.cellAt sourceMountain ⟨sourceColumn, startIndex + position + 1⟩ = .ok execution.lower :=
  cellAt_ok_iff.mpr ⟨nodes, hColumn, execution.lower_at⟩

theorem ContourAdjacentExecution.upper_cellAt {sourceMountain : Mountain}
    (hColumn : sourceMountain[sourceColumn]? = some nodes) :
    Canonical.cellAt sourceMountain ⟨sourceColumn, startIndex + position + 2⟩ = .ok execution.upper :=
  cellAt_ok_iff.mpr ⟨nodes, hColumn, execution.upper_at⟩

end SourceReads

theorem contour_adjacent_execution {mountain : Mountain} {sourceColumn shift rootColumn : Nat}
    {nodes : Column} (hPower : ColumnPowerSteps nodes) (markerIndices : List Nat)
    {root target : Row} {index : Nat} {current : Cell}
    (hCurrent : nodes[index]? = some current) (hRoot : root ≤ current.row)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest)
    {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index
      (Row.lift root target current.row) current rest = .ok result)
    {position : Nat} {copiedLower copiedUpper : Cell}
    (hLower : result[position]? = some copiedLower)
    (hUpper : result[position + 1]? = some copiedUpper) :
    Nonempty (ContourAdjacentExecution mountain sourceColumn markerIndices shift rootColumn nodes
      root target index result position copiedLower copiedUpper) := by
  obtain ⟨low⟩ := contour_execution_at hPower markerIndices hCurrent hRoot hRest hRun hLower
  obtain ⟨high⟩ := contour_execution_at hPower markerIndices hCurrent hRoot hRest hRun hUpper
  have hMiddle : high.lower = low.upper := Option.some.inj
    (high.lower_at.symm.trans (by simpa only [Nat.add_assoc] using low.upper_at))
  exact ⟨{
    lower := low.upper
    upper := high.upper
    tail := high.tail
    lower_at := low.upper_at
    upper_at := by simpa only [Nat.add_assoc] using high.upper_at
    root_lower := low.root_lower.trans low.source_rows.le
    source_rows := by simpa only [hMiddle] using high.source_rows
    lower_not_one := by simpa only [hMiddle] using high.lower_not_one
    lower_nonzero := low.upper_nonzero
    upper_nonzero := high.upper_nonzero
    no_markers := by
      intro middle hLow hHigh
      exact high.no_markers middle hLow (by omega)
    lower_copy := low.copy_run
    upper_copy := by simpa only [Nat.add_assoc] using high.copy_run
    suffix_run := by simpa only [Nat.add_assoc] using high.suffix_run
    result_drop := by simpa only [Nat.add_assoc] using high.result_drop
    lower_row := low.copied_row
    upper_row := high.copied_row }⟩

/-- Specialize the common lift to the initial marker's actual source row.
The requested target itself is used in the real initial contour call. -/
theorem contour_adjacent_source {mountain : Mountain} {sourceColumn shift rootColumn : Nat}
    {nodes : Column} (hPower : ColumnPowerSteps nodes) (markerIndices : List Nat)
    {index : Nat} {current : Cell} (target : Row)
    (hCurrent : nodes[index]? = some current)
    {rest : List Cell} (hRest : nodes.toList.drop (index + 1) = rest)
    {result : List Cell}
    (hRun : contour mountain sourceColumn markerIndices shift rootColumn index target current rest = .ok result)
    {position : Nat} {copiedLower copiedUpper : Cell}
    (hLower : result[position]? = some copiedLower)
    (hUpper : result[position + 1]? = some copiedUpper) :
    Nonempty (ContourAdjacentExecution mountain sourceColumn markerIndices shift rootColumn nodes
      current.row target index result position copiedLower copiedUpper) := by
  apply contour_adjacent_execution hPower markerIndices hCurrent le_rfl hRest _ hLower hUpper
  simpa only [Row.lift_at_root] using hRun

theorem ColumnCopyData.contour_inside_source
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    {marker : Ref} (hm : marker ∈ d.bucket) {path : List Cell}
    (hRun : contour mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn marker.index
      (d.marker_data marker hm).targetCell.row (d.marker_data marker hm).current
      (d.sources.toList.drop (marker.index + 1)) = .ok path)
    {position : Nat} {copiedLower copiedUpper : Cell}
    (hLower : path[position]? = some copiedLower)
    (hUpper : path[position + 1]? = some copiedUpper) :
    Nonempty (ContourAdjacentExecution mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn
      d.sources (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row
      marker.index path position copiedLower copiedUpper) :=
  contour_adjacent_source d.source_power (d.bucket.map Ref.index)
    (d.marker_data marker hm).targetCell.row (d.marker_data marker hm).current_at rfl hRun hLower hUpper

/-- The unresolved contour-inside origin now carries the actual consecutive
source reads and copy executions. SameShape transfers the row and stored
left endpoint to the caller's actual finished nodes; copied values are not
identified with their subsequently reconstructed output values. -/
theorem ExecutedSegmentPair.contour_inside_source
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {index : Nat} {lower upper : Cell} (pair : ExecutedSegmentPair d index lower upper)
    {position : Nat} (hLower : pair.path[position]? = some pair.originalLower)
    (hUpper : pair.path[position + 1]? = some pair.originalUpper) :
    ∃ execution : ContourAdjacentExecution mountain sourceColumn (d.bucket.map Ref.index) shift rootColumn
        d.sources (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row
        pair.marker.index pair.path position pair.originalLower pair.originalUpper,
      lower.row = Row.lift (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row execution.lower.row ∧
      upper.row = Row.lift (d.marker_data pair.marker pair.member).current.row
        (d.marker_data pair.marker pair.member).targetCell.row execution.upper.row ∧
      lower.left = pair.originalLower.left ∧ upper.left = pair.originalUpper.left := by
  obtain ⟨execution⟩ := d.contour_inside_source pair.member pair.contour_run hLower hUpper
  exact ⟨execution, pair.lower_shape.1.symm.trans execution.lower_row,
    pair.upper_shape.1.symm.trans execution.upper_row, pair.lower_shape.2.symm, pair.upper_shape.2.symm⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.contour_execution_at
#print axioms OmegaY.Expansion.contour_adjacent_execution
#print axioms OmegaY.Expansion.ColumnCopyData.contour_inside_source
#print axioms OmegaY.Expansion.ExecutedSegmentPair.contour_inside_source
