/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SecondValid.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.SecondColumnCandidates
import OmegaY.Expansion.SecondBaseRows
import OmegaY.Expansion.SegmentLegs

/-! The second actual copied column finishes and is appendable. Its parent
may lie in the first copied column, whose canonical normality and adjacent
power steps are not assumed. This still concerns only the first block. -/

namespace OmegaY.Expansion

open Canonical

theorem Preparation.second_copyColumn_valid {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {firstColumn : Column}
    (hCopy : copyColumn p.reduced p.marked references (p.root.column + 1)
      (p.initial.size - 1 - p.root.column) p.root.column = .ok firstColumn)
    (hSecond : p.root.column + 2 < p.reduced.size) :
    ∃ column,
      copyColumn (p.reduced.push firstColumn) p.marked references (p.root.column + 2)
        (p.initial.size - 1 - p.root.column) p.root.column = .ok column ∧
      FinishedColumn (p.reduced.push firstColumn) column ∧
      ColumnValid (p.reduced.push firstColumn) (p.reduced.push firstColumn).size column ∧
      TopOne column ∧ MountainValid ((p.reduced.push firstColumn).push column) := by
  obtain ⟨sources, segments, hBaseSources, hSources, hSegments, hNodup, hPositive, hColumn⟩ :=
    p.second_copyColumn_candidates hLast hMap hCopy hSecond
  have hRuns := fun marker hMarker => (hSegments marker hMarker).1
  have hInput : FinishInput (p.reduced.push firstColumn)
      ((p.marked[p.root.column + 2]?.getD []).flatMap segments) := {
    rows_nodup := hNodup
    phantom_mem := p.second_candidates_phantom hLast hMap hCopy hBaseSources segments hRuns
    bottom_mem := List.mem_map.mp
      (p.second_candidates_one hLast hMap hCopy hBaseSources segments hRuns)
    parents_above_one := hPositive }
  have hDestination : p.root.column + 2 + (p.reduced.size - 1 - p.root.column) =
      (p.reduced.push firstColumn).size := by
    simp only [Array.size_push]
    omega
  have hLegs : ∀ cell ∈ (p.marked[p.root.column + 2]?.getD []).flatMap segments,
      CellLegs (p.reduced.push firstColumn) (p.reduced.push firstColumn).size cell := by
    intro cell hCell
    obtain ⟨marker, hMarker, hCell⟩ := List.mem_flatMap.mp hCell
    obtain ⟨d⟩ := p.second_segment_data hLast hMap hCopy hMarker
    have hSourcesEq : d.sources = sources := Option.some.inj (d.source_column.symm.trans hSources)
    have hRun := hRuns marker hMarker
    rw [← hSourcesEq] at hRun
    have hResult := copySegment_legs_of_source d.ambient_valid d.source_column (by omega)
      d.destination d.source_top d.source_power references _ d.current_at d.upper_at
      d.upper_left d.parent_nodes d.target_at d.reference d.target_lower hRun cell hCell
    exact hDestination ▸ hResult
  obtain ⟨column, hFinish, _, hFinished, hValid, hTop⟩ := hInput.finish_valid
    (by simp only [Array.size_push]; omega)
    (fun cell hCell => (hLegs cell hCell).1)
    (fun cell hCell => (hLegs cell hCell).2)
  obtain ⟨first, hFirst, _, _, _, hAmbient⟩ := p.initial_copyColumn_valid hLast hMap
  have he : first = firstColumn := Except.ok.inj (hFirst.symm.trans hCopy)
  subst first
  exact ⟨column, hColumn.trans hFinish, hFinished, hValid, hTop, hAmbient.push hValid⟩

/-- Every prepared input with a second source supplies its reference map
and the first two completed columns. No first-copy success or new-graph
certificate is supplied by the caller. Both calls use the original width. -/
theorem Preparation.initial_two_columns_valid {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last)
    (hSecond : p.root.column + 2 < p.reduced.size) :
    ∃ (references : List Ref) (first second : Column),
      p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references ∧
      copyColumn p.reduced p.marked references (p.root.column + 1)
        (p.initial.size - 1 - p.root.column) p.root.column = .ok first ∧
      copyColumn (p.reduced.push first) p.marked references (p.root.column + 2)
        (p.initial.size - 1 - p.root.column) p.root.column = .ok second ∧
      MountainValid ((p.reduced.push first).push second) ∧ TopOne first ∧ TopOne second := by
  obtain ⟨references, first, hMap, hFirst, _, _, hFirstTop, _, _⟩ := p.initial_first_copy_valid hLast
  obtain ⟨second, hSecondCopy, _, _, hSecondTop, hValid⟩ :=
    p.second_copyColumn_valid hLast hMap hFirst hSecond
  exact ⟨references, first, second, hMap, hFirst, hSecondCopy, hValid, hFirstTop, hSecondTop⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.second_copyColumn_valid
#print axioms OmegaY.Expansion.Preparation.initial_two_columns_valid
