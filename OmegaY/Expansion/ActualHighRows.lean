/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighRows.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMarkerCaps
import OmegaY.Expansion.HighRowPreservation
import OmegaY.Expansion.CopyRunHistory

/-!
# High-row support in the actual dynamic copying process

The common threshold is the original last top. Its marker caps are
obtained from the current block's actual boundary partition. Execution
history then transports the result to previously completed columns and
to the final boundary of a whole block. No high-tail invariant, copied
normality, or agreement of numerical values is assumed.
-/

namespace OmegaY.Expansion

open Canonical

/-- A successful current-column copy has exactly the frozen source's
rows at or above the original last top. All cap and source-geometry
premises are derived from the actual dynamic state. -/
theorem DynamicBlockState.copyColumn_high_rows_iff
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (hLast : 1 < last) (hNext : next < p.reduced.size)
    {source column : Column} (hSource : p.reduced[next]? = some source)
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column)
    {row : Row} (hHigh : p.lastTop.row ≤ row) :
    row ∈ column.toList.map Cell.row ↔ row ∈ source.toList.map Cell.row := by
  obtain ⟨d, hNoPremature, _, _⟩ := s.column_data hLast hNext
  have hFrozen : p.reduced[next]? = some d.sources :=
    (s.base_ambient next hNext).symm.trans d.source_column
  have hSame : d.sources = source := Option.some.inj (hFrozen.symm.trans hSource)
  simpa only [hSame] using d.copyColumn_high_rows_iff
    (s.marker_caps_below_lastTop hLast d hNext) hNoPremature hRun hHigh

/-- Any already copied source column has an actual current read, and its
high-row support still agrees with the original frozen source column. -/
theorem DynamicBlockState.copied_column_high_rows
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient)
    (hLast : 1 < last) {sourceColumn : Nat}
    (hRight : p.root.column < sourceColumn) (hBefore : sourceColumn < next)
    {source : Column} (hSource : p.reduced[sourceColumn]? = some source) :
    ∃ column,
      ambient[sourceColumn + block * (p.reduced.size - 1 - p.root.column)]? = some column ∧
      ∀ row, p.lastTop.row ≤ row →
        (row ∈ column.toList.map Cell.row ↔ row ∈ source.toList.map Cell.row) := by
  obtain ⟨before, column, oldState, hRun, _, hRead⟩ := history.column_read hRight hBefore
  refine ⟨column, hRead, fun row hHigh => ?_⟩
  exact oldState.copyColumn_high_rows_iff hLast (hBefore.trans_le s.next_upper)
    hSource hRun hHigh

/-- The actual completed block, with fresh references selected by the
engine, has a boundary column whose high-row support is exactly the
reduced mountain's original last-column support. -/
theorem BlockReady.copyBlock_with_high_boundary
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} (ready : BlockReady p block start)
    (hLast : 1 < last) :
    ∃ result sourceLast copiedLast,
      OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result ∧
      p.reduced[p.reduced.size - 1]? = some sourceLast ∧
      result[result.size - 1]? = some copiedLast ∧
      ∀ row, p.lastTop.row ≤ row →
        (row ∈ copiedLast.toList.map Cell.row ↔ row ∈ sourceLast.toList.map Cell.row) := by
  obtain ⟨result, references, hRun, hReady, _, hState, history⟩ :=
    ready.copyBlock_with_history hLast
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hRoot := p.root_before_last
  have hLastIndex : p.reduced.size - 1 < p.reduced.size := by omega
  let sourceLast := p.reduced[p.reduced.size - 1]
  have hSource : p.reduced[p.reduced.size - 1]? = some sourceLast :=
    Array.getElem?_eq_getElem hLastIndex
  obtain ⟨copiedLast, hCopied, hRows⟩ := hState.copied_column_high_rows history hLast
    (by omega : p.root.column < p.reduced.size - 1) hLastIndex hSource
  have hBoundary : p.reduced.size - 1 + block * (p.reduced.size - 1 - p.root.column) =
      result.size - 1 := by have := hState.size_eq; omega
  exact ⟨result, sourceLast, copiedLast, hRun, hReady, hSource, hBoundary ▸ hCopied, hRows⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.copyColumn_high_rows_iff
#print axioms OmegaY.Expansion.DynamicBlockState.copied_column_high_rows
#print axioms OmegaY.Expansion.BlockReady.copyBlock_with_high_boundary
