/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialFinish.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.InitialColumnNodup
import OmegaY.Expansion.InitialBaseRows
import OmegaY.Expansion.InitialSegmentPositive

/-! The first actual copied column now passes the original finisher.
All sorting and numerical backfill inputs come from preparation. This does
not assert canonical reconstruction, later-column preservation, or descent. -/

namespace OmegaY.Expansion

open Canonical

theorem Preparation.initial_size_eq_reduced_size {front : List Nat} {last : Nat}
    (p : Preparation front last) : p.initial.size = p.reduced.size := by
  have hInitial := build_size p.initial_build
  have hReduced := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hInitial hReduced
  exact hInitial.trans hReduced.symm

theorem Preparation.initial_candidates_finish_input {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {sources : Column} (hSources : p.reduced[p.root.column + 1]? = some sources)
    (segments : Ref → List Cell)
    (hSegments : ∀ marker ∈ p.marked[p.root.column + 1]?.getD [],
      copySegment p.reduced sources references (p.root.column + 1)
        ((p.marked[p.root.column + 1]?.getD []).map Ref.index)
        (p.reduced.size - 1 - p.root.column) p.root.column marker.index = .ok (segments marker)) :
    FinishInput p.reduced ((p.marked[p.root.column + 1]?.getD []).flatMap segments) := by
  refine {
    rows_nodup := p.initial_segments_rows_nodup hLast hMap hSources segments hSegments
    phantom_mem := p.initial_candidates_phantom hLast hMap hSources segments hSegments
    bottom_mem := ?_
    parents_above_one := p.initial_candidates_positive_parents hLast hMap hSources segments hSegments }
  exact List.mem_map.mp (p.initial_candidates_one hLast hMap hSources segments hSegments)

/-- The reference map may be any actual successful output; determinism
identifies it with the preparation-supplied output. Finish success is proved,
not supplied as an input. The width here is the original engine's width. -/
theorem Preparation.initial_copyColumn_total {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∃ column,
      copyColumn p.reduced p.marked references (p.root.column + 1)
        (p.initial.size - 1 - p.root.column) p.root.column = .ok column ∧
      FinishedColumn p.reduced column := by
  obtain ⟨otherReferences, sources, segments, hOtherMap, hSources, hSegments, _, hColumn⟩ :=
    p.initial_copyColumn_candidates_nodup hLast
  have he : otherReferences = references := Except.ok.inj (hOtherMap.symm.trans hMap)
  subst otherReferences
  have hInput := p.initial_candidates_finish_input hLast hMap hSources segments
    (fun marker hMarker => (hSegments marker hMarker).1)
  obtain ⟨column, hFinish, _, hFinished⟩ := hInput.finish
  refine ⟨column, ?_, hFinished⟩
  rw [p.initial_size_eq_reduced_size]
  exact hColumn.trans hFinish

/-- A nontrivial prepared input supplies both the reference map and a fully
numerically finished first copied column, without additional support inputs. -/
theorem Preparation.initial_first_copy_exists {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) :
    ∃ references column,
      p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references ∧
      copyColumn p.reduced p.marked references (p.root.column + 1)
        (p.initial.size - 1 - p.root.column) p.root.column = .ok column ∧
      FinishedColumn p.reduced column := by
  obtain ⟨references, hMap, _⟩ := p.initial_references hLast
  obtain ⟨column, hColumn, hFinished⟩ := p.initial_copyColumn_total hLast hMap
  exact ⟨references, column, hMap, hColumn, hFinished⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_copyColumn_total
#print axioms OmegaY.Expansion.Preparation.initial_first_copy_exists
