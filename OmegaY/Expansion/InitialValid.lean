/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialValid.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialFinish
import OmegaY.Expansion.InitialCandidateLegs
import OmegaY.Expansion.FinishPreservation
import OmegaY.Expansion.AppendLocality

/-! The first copied column succeeds and can actually be appended while
preserving MountainValid. This local validity does not assert the canonical
numerical parent-search rule, adjacent power steps, or later-copy support. -/

namespace OmegaY.Expansion

open Canonical

theorem Preparation.initial_copyColumn_valid {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∃ column,
      copyColumn p.reduced p.marked references (p.root.column + 1)
        (p.initial.size - 1 - p.root.column) p.root.column = .ok column ∧
      FinishedColumn p.reduced column ∧ ColumnValid p.reduced p.reduced.size column ∧
      TopOne column ∧ MountainValid (p.reduced.push column) := by
  obtain ⟨otherReferences, sources, segments, hOtherMap, hSources, hSegments, _, hColumn⟩ :=
    p.initial_copyColumn_candidates_nodup hLast
  have he : otherReferences = references := Except.ok.inj (hOtherMap.symm.trans hMap)
  subst otherReferences
  have hRuns := fun marker hMarker => (hSegments marker hMarker).1
  have hInput := p.initial_candidates_finish_input hLast hMap hSources segments hRuns
  have hLegs := p.initial_candidate_legs hLast hMap hSources segments hRuns
  have hSize : 0 < p.reduced.size := by have := p.reduced_last_exists; omega
  obtain ⟨column, hFinish, _, hFinished, hValid, hTop⟩ := hInput.finish_valid hSize
    (fun cell hCell => (hLegs cell hCell).1)
    (fun cell hCell => (hLegs cell hCell).2)
  refine ⟨column, ?_, hFinished, hValid, hTop, p.reduced_valid.push hValid⟩
  rw [p.initial_size_eq_reduced_size]
  exact hColumn.trans hFinish

/-- Preparation supplies the map, the actual completed first copied column,
and an extended valid mountain. Its old block references remain usable with
exactly the same referenceAt results after the append. -/
theorem Preparation.initial_first_copy_valid {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) :
    ∃ references column,
      p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references ∧
      copyColumn p.reduced p.marked references (p.root.column + 1)
        (p.initial.size - 1 - p.root.column) p.root.column = .ok column ∧
      FinishedColumn p.reduced column ∧ ColumnValid p.reduced p.reduced.size column ∧
      TopOne column ∧ MountainValid (p.reduced.push column) ∧
      ∀ row, referenceAt (p.reduced.push column) references row = referenceAt p.reduced references row := by
  obtain ⟨references, hMap, _⟩ := p.initial_references hLast
  obtain ⟨column, hCopy, hFinished, hValid, hTop, hPush⟩ := p.initial_copyColumn_valid hLast hMap
  exact ⟨references, column, hMap, hCopy, hFinished, hValid, hTop, hPush,
    fun row => (PreservesColumns.push p.reduced column).referenceAt
      (p.initial_references_valid hMap) row⟩

/-- The preparation premise is inhabited for every nontrivial legal input.
There is no restriction on the length, entries, or ordinal row degrees. -/
theorem initial_first_copy_of_legal_input (middle : List Nat) (last : Nat)
    (hMiddle : ∀ value ∈ middle, 0 < value) (hLast : 1 < last) :
    ∃ (p : Preparation (1 :: middle) last) (references : List Ref) (column : Column),
      p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references ∧
      copyColumn p.reduced p.marked references (p.root.column + 1)
        (p.initial.size - 1 - p.root.column) p.root.column = .ok column ∧
      FinishedColumn p.reduced column ∧ ColumnValid p.reduced p.reduced.size column ∧
      TopOne column ∧ MountainValid (p.reduced.push column) := by
  obtain ⟨p⟩ := preparation_total middle last hMiddle hLast
  obtain ⟨references, column, hMap, hCopy, hFinished, hValid, hTop, hPush, _⟩ :=
    p.initial_first_copy_valid hLast
  exact ⟨p, references, column, hMap, hCopy, hFinished, hValid, hTop, hPush⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_copyColumn_valid
#print axioms OmegaY.Expansion.Preparation.initial_first_copy_valid
#print axioms OmegaY.Expansion.initial_first_copy_of_legal_input
