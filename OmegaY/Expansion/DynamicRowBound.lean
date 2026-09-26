/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DynamicRowBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ColumnRowBound
import OmegaY.Expansion.DynamicBlockStep
import OmegaY.Canonical.DecrementRows

/-!
# A fixed mountain-row bound through a dynamic column step

The bound is stated on actual cellAt reads. It restricts to old columns,
survives deletion of the last column, and is inherited by the exact
decrement/graft construction. Fresh dynamic block references use the same
original last-top cap, independently of the number of earlier copies.
-/

namespace OmegaY.Expansion

open Canonical

def MountainRowsBound (mountain : Mountain) (height : Row) : Prop :=
  ∀ (ref : Ref) (cell : Cell), Canonical.cellAt mountain ref = .ok cell → cell.row ≤ height

theorem MountainRowsBound.column {mountain : Mountain} {height : Row}
    (hBound : MountainRowsBound mountain height) {columnIndex : Nat} {column : Column}
    (hColumn : mountain[columnIndex]? = some column) : ColumnRowsBound column height := by
  intro index cell hCell
  exact hBound ⟨columnIndex, index⟩ cell (cellAt_ok_iff.mpr ⟨column, hColumn, hCell⟩)

theorem MountainRowsBound.of_columns {mountain : Mountain} {height : Row}
    (hBound : ∀ (columnIndex : Nat) (column : Column), mountain[columnIndex]? = some column →
      ColumnRowsBound column height) : MountainRowsBound mountain height := by
  intro ref cell hCell
  obtain ⟨column, hColumn, hRead⟩ := cellAt_ok_iff.mp hCell
  exact hBound ref.column column hColumn ref.index cell hRead

/-- A bound on a larger mountain restricts to all unchanged old columns.
The reverse implication would require bounds for the newly appended columns. -/
theorem MountainRowsBound.restrict {before after : Mountain} {height : Row}
    (hBound : MountainRowsBound after height) (hPreserve : PreservesColumns before after) :
    MountainRowsBound before height := by
  intro ref cell hCell
  obtain ⟨column, hColumn, hRead⟩ := cellAt_ok_iff.mp hCell
  exact hBound ref cell (cellAt_ok_iff.mpr ⟨column, hPreserve.column_read hColumn, hRead⟩)

theorem MountainRowsBound.push {mountain : Mountain} {height : Row}
    (hBound : MountainRowsBound mountain height) {column : Column}
    (hColumn : ColumnRowsBound column height) : MountainRowsBound (mountain.push column) height := by
  apply MountainRowsBound.of_columns
  intro columnIndex nodes hNodes
  by_cases hLast : columnIndex = mountain.size
  · have he : column = nodes := by
      simpa only [hLast, Array.getElem?_push_size, Option.some.injEq] using hNodes
    exact he ▸ hColumn
  · have hOld : mountain[columnIndex]? = some nodes := by
      simpa only [Array.getElem?_push, hLast, ↓reduceIte] using hNodes
    exact hBound.column hOld

theorem MountainRowsBound.pop {mountain : Mountain} {height : Row}
    (hBound : MountainRowsBound mountain height) : MountainRowsBound mountain.pop height := by
  apply MountainRowsBound.of_columns
  intro columnIndex column hColumn
  have hIndex := (Array.getElem?_eq_some_iff.mp hColumn).1
  have hOld : mountain[columnIndex]? = some column := by
    simpa only [Array.getElem?_pop, if_pos (by simpa only [Array.size_pop] using hIndex)] using hColumn
  exact hBound.column hOld

theorem MountainRowsBound.rows_subset {before after : Mountain} {height : Row}
    (hBound : MountainRowsBound before height) (hSubset : Canonical.RowsSubset after before) :
    MountainRowsBound after height := by
  intro ref cell hCell
  have hNew : RowOccurs after cell.row := rowOccurs_iff_cellAt.mpr ⟨ref, cell, hCell, rfl⟩
  obtain ⟨oldRef, oldCell, hOld, hRow⟩ := rowOccurs_iff_cellAt.mp (hSubset cell.row hNew)
  exact hRow ▸ hBound oldRef oldCell hOld

/-- The actual decrement and graft introduces no row above the old global
bound. This uses the already proved exact row-support inclusion. -/
theorem Preparation.reduced_rows_bound {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {height : Row}
    (hBound : MountainRowsBound p.initial height) : MountainRowsBound p.reduced height :=
  hBound.rows_subset (build_decrement_rows_subset p.initial_build p.reduced_build hLast)

theorem Preparation.lastTop_row_bound {front : List Nat} {last : Nat}
    (p : Preparation front last) {height : Row} (hBound : MountainRowsBound p.initial height) :
    p.lastTop.row ≤ height := by
  have hTop := p.initial_top
  cases hColumn : p.initial[front.length]? with
  | none => simp only [hColumn, Option.bind_none, reduceCtorEq] at hTop
  | some column =>
    have hBack : column.back? = some p.lastTop := by
      simpa only [hColumn, Option.bind_some] using hTop
    have hRead : column[column.size - 1]? = some p.lastTop := by
      simpa only [Array.back?_eq_getElem?] using hBack
    exact hBound ⟨front.length, column.size - 1⟩ p.lastTop
      (cellAt_ok_iff.mpr ⟨column, hColumn, hRead⟩)

/-- The next actual copy has the same fixed row bound in any block. The
ambient mountain may contain any number of already completed copied columns. -/
theorem DynamicBlockState.copy_next_rows_bound {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) (hNext : next < p.reduced.size) {height : Row}
    (hReducedBound : MountainRowsBound p.reduced height) (hLastTop : p.lastTop.row ≤ height)
    {column : Column}
    (hCopy : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ColumnRowsBound column height := by
  obtain ⟨d, _, _, _⟩ := s.column_data hLast hNext
  have hBaseSource : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hBoundaryRows : RootRowsInColumn p ambient (start.size - 1) :=
    RootRowsInColumn.preserve s.boundary_rows s.start_preserved
  have hMap : p.boundaries.mapM (below ambient (start.size - 1)) = .ok references := by
    have hBelow : below ambient (start.size - 1) = below start (start.size - 1) :=
      funext (s.start_preserved.below (RootRowsInColumn.column_lt s.boundary_rows))
    rw [hBelow]
    exact s.reference_map
  exact d.copyColumn_rows_bound_of_boundary hLast hBaseSource hBoundaryRows hMap
    (hReducedBound.column hBaseSource) hLastTop hCopy

theorem DynamicBlockState.copy_next_push_rows_bound {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start : Mountain} {references : List Ref}
    {next : Nat} {ambient : Mountain} (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) (hNext : next < p.reduced.size) {height : Row}
    (hReducedBound : MountainRowsBound p.reduced height) (hLastTop : p.lastTop.row ≤ height)
    (hAmbientBound : MountainRowsBound ambient height) {column : Column}
    (hCopy : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    MountainRowsBound (ambient.push column) height :=
  hAmbientBound.push (s.copy_next_rows_bound hLast hNext hReducedBound hLastTop hCopy)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.MountainRowsBound.pop
#print axioms OmegaY.Expansion.Preparation.reduced_rows_bound
#print axioms OmegaY.Expansion.DynamicBlockState.copy_next_rows_bound
