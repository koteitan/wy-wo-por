/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/HistoryRawInvariants.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.HistoryPrefix
import OmegaY.Expansion.BlocksRawGeometry
import OmegaY.Expansion.BlocksRawFatherBound

/-!
# Actual raw invariants at every recorded within-block state

The completed outer-loop prefix supplies the block-start geometry. Every
later column is recovered from its actual history, including its earlier
history when a selector needs it. Complete-column preservation transports
both selected parents and their upper successors into the current ambient.
No numerical parent identification or copied Normal is a premise.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem DynamicBlockState.new_column_source
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    {c : Nat} (hc : c < ambient.size) (hNew : ¬ c < start.size) :
    ∃ sourceColumn, p.root.column < sourceColumn ∧ sourceColumn < next ∧
      sourceColumn + block * (p.reduced.size - 1 - p.root.column) = c := by
  refine ⟨c - block * (p.reduced.size - 1 - p.root.column), ?_, ?_, ?_⟩ <;>
    have hStartSize := s.start_size <;> have hSize := s.size_eq <;> omega

/-- Raw row geometry for the current mountain follows from the actual
block-start run and the actual earlier column executions. The outer prefix
is needed by the copied-root selector, not as a copied-normality premise. -/
theorem DynamicBlockState.mountainRawGeometry_of_start_run
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start) : MountainRawGeometry ambient := by
  have hStart := p.blocks_raw_geometry_of_run hLast hStartRun
  intro c hc
  by_cases hOld : c < start.size
  · have hRead : ambient[c]? = some start[c] :=
      s.start_preserved.column_read (Array.getElem?_eq_getElem hOld)
    have hEq : start[c] = ambient[c] := Option.some.inj
      (hRead.symm.trans (Array.getElem?_eq_getElem hc))
    rw [← hEq]
    exact (hStart c hOld).transport
      (fun ref hr => (s.start_preserved.cellAt (hr.trans hOld)).symm)
  · obtain ⟨sourceColumn, hLower, hUpper, hIndex⟩ := s.new_column_source hc hOld
    obtain ⟨before, column, state, oldHistory, hRun, hPreserve, hRead⟩ :=
      history.column_with_history hLower hUpper
    have hReadAt : ambient[c]? = some column := by simpa only [hIndex] using hRead
    have hEq : column = ambient[c] := Option.some.inj
      (hReadAt.symm.trans (Array.getElem?_eq_getElem hc))
    rw [← hEq]
    have hSourceBound : sourceColumn < p.reduced.size := hUpper.trans_le s.next_upper
    obtain ⟨actual, hActual, hValid, _, _, _, _, _⟩ := state.copy_next hLast hSourceBound
    have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
    subst actual
    have hBeforeSize : before.size = c := state.size_eq.trans hIndex
    have hColumn : ColumnRawGeometry (before.push column) before.size column := by
      intro index lower upper hLowerRead hUpperRead hReal
      have hPositive := hValid.rows_strict 0 index phantom lower hValid.phantom hLowerRead hReal
      have hNonzero : lower.row ≠ 0 := by
        change (0 : Row) < lower.row at hPositive
        exact ne_of_gt hPositive
      exact state.actual_adjacent_raw_geometry oldHistory hLast hStartRun hSourceBound hRun
        hLowerRead hUpperRead hNonzero
    have hCopied : ColumnRawGeometry ambient before.size column := hColumn.transport
      (fun ref hr => (hPreserve.cellAt (by simp only [Array.size_push]; omega)).symm)
    simpa only [hBeforeSize] using hCopied

/-- The raw father-upper bound needs only the initial bound and actual
column history. Unlike copied-root selection, its local proof does not
require an outer-loop prefix equation. -/
theorem DynamicBlockState.mountainRawFatherBound_of_history
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStart : MountainRawFatherBound start) : MountainRawFatherBound ambient := by
  intro c hc
  by_cases hOld : c < start.size
  · have hRead : ambient[c]? = some start[c] :=
      s.start_preserved.column_read (Array.getElem?_eq_getElem hOld)
    have hEq : start[c] = ambient[c] := Option.some.inj
      (hRead.symm.trans (Array.getElem?_eq_getElem hc))
    rw [← hEq]
    exact (hStart c hOld).transport (s.start_valid c hOld)
      (fun ref hr => s.start_preserved.cellAt (hr.trans hOld))
  · obtain ⟨sourceColumn, hLower, hUpper, hIndex⟩ := s.new_column_source hc hOld
    obtain ⟨before, column, state, hRun, hPreserve, hRead⟩ :=
      history.column_read hLower hUpper
    have hReadAt : ambient[c]? = some column := by simpa only [hIndex] using hRead
    have hEq : column = ambient[c] := Option.some.inj
      (hReadAt.symm.trans (Array.getElem?_eq_getElem hc))
    rw [← hEq]
    have hSourceBound : sourceColumn < p.reduced.size := hUpper.trans_le s.next_upper
    obtain ⟨actual, hActual, hValid, _, _, _, _, _⟩ := state.copy_next hLast hSourceBound
    have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
    subst actual
    have hBefore : PreservesColumns before ambient :=
      (PreservesColumns.push before column).trans hPreserve
    intro index lower upper _ hUpperRead _
    exact (state.actual_copyColumn_father_bound hLast hSourceBound hRun
      (index + 1) upper hUpperRead).preserve hBefore
        (fun ref hLeft => (hValid.stored_valid _ _ _ hUpperRead hLeft).1)

/-- Actual outer execution discharges the incoming raw father bound. -/
theorem DynamicBlockState.mountainRawFatherBound_of_start_run
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start) : MountainRawFatherBound ambient :=
  s.mountainRawFatherBound_of_history history hLast
    (p.blocks_raw_father_bound_of_run hLast hStartRun)

/-- Typed raw geometry and father barriers are conclusions of real
execution; callers need not provide either certificate. -/
theorem DynamicBlockState.raw_invariants_of_start_run
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block copies : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start) :
    (Frame.ofMountain ambient).RawRowGeometry ∧
      (Frame.ofMountain ambient).RawFatherUpperBound :=
  ⟨(s.mountainRawGeometry_of_start_run history hLast hStartRun).rawRowGeometry,
    (s.mountainRawFatherBound_of_start_run history hLast hStartRun).rawFatherUpperBound⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.mountainRawGeometry_of_start_run
#print axioms OmegaY.Expansion.DynamicBlockState.mountainRawFatherBound_of_history
#print axioms OmegaY.Expansion.DynamicBlockState.mountainRawFatherBound_of_start_run
#print axioms OmegaY.Expansion.DynamicBlockState.raw_invariants_of_start_run
