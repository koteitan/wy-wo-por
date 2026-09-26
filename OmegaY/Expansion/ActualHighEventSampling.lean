/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighEventSampling.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighRows
import OmegaY.Expansion.FrontierCuts
import OmegaY.Expansion.LoopPrefix

/-!
# Exact high-event support of actual finite copying blocks

All cells at or above the original last top come from an actual frozen
reduced-source cell with the same row. This is proved for every column,
including old columns from earlier blocks, by actual column histories and
outer-loop induction. Complete source-column preservation supplies the
reverse inclusion. The sorted high event lists therefore agree exactly.

These are row-event statements before the final pop. They identify neither
numerical values nor event-parent maps.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Every actual high cell has a real read in the frozen reduced source.
Only its row is identified; the value and stored parent may differ. -/
def HighRowsFromSource {front : List Nat} {last : Nat} (p : Preparation front last)
    (mountain : Mountain) : Prop :=
  ∀ ref cell, Canonical.cellAt mountain ref = .ok cell → p.lastTop.row ≤ cell.row →
    ∃ sourceRef sourceCell, Canonical.cellAt p.reduced sourceRef = .ok sourceCell ∧
      sourceCell.row = cell.row

/-- The actual history covers every new column, not only the boundary.
Existing columns use the incoming high-row fact and complete preservation. -/
theorem DynamicBlockState.high_rows_from_source
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    (hStart : HighRowsFromSource p start) : HighRowsFromSource p ambient := by
  intro ref cell hRead hHigh
  obtain ⟨nodes, hNodes, hCell⟩ := cellAt_ok_iff.mp hRead
  have hc := (Array.getElem?_eq_some_iff.mp hNodes).1
  by_cases hOld : ref.column < start.size
  · exact hStart ref cell ((s.start_preserved.cellAt hOld).symm.trans hRead) hHigh
  · obtain ⟨sourceColumn, hRight, hBefore, hIndex⟩ :
        ∃ sourceColumn, p.root.column < sourceColumn ∧ sourceColumn < next ∧
          sourceColumn + block * (p.reduced.size - 1 - p.root.column) = ref.column := by
      refine ⟨ref.column - block * (p.reduced.size - 1 - p.root.column), ?_, ?_, ?_⟩ <;>
        have hStartSize := s.start_size <;> have hSize := s.size_eq <;> omega
    have hSourceBound : sourceColumn < p.reduced.size := hBefore.trans_le s.next_upper
    have hSource : p.reduced[sourceColumn]? = some p.reduced[sourceColumn] :=
      Array.getElem?_eq_getElem hSourceBound
    obtain ⟨column, hColumn, hRows⟩ := s.copied_column_high_rows history hLast hRight hBefore hSource
    have hColumnAt : ambient[ref.column]? = some column := by simpa only [hIndex] using hColumn
    have hColumnEq : column = nodes := Option.some.inj (hColumnAt.symm.trans hNodes)
    subst column
    have hMember : cell.row ∈ nodes.toList.map Cell.row := List.mem_map.mpr
      ⟨cell, List.mem_of_getElem? (by simpa only [Array.getElem?_toList] using hCell), rfl⟩
    obtain ⟨sourceCell, hSourceMember, hRow⟩ := List.mem_map.mp ((hRows cell.row hHigh).mp hMember)
    obtain ⟨sourceIndex, hSourceAt⟩ := List.mem_iff_getElem?.mp hSourceMember
    exact ⟨⟨sourceColumn, sourceIndex⟩, sourceCell, cellAt_ok_iff.mpr
      ⟨p.reduced[sourceColumn], hSource, by simpa only [Array.getElem?_toList] using hSourceAt⟩, hRow⟩

theorem BlockReady.copyBlock_with_high_rows
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} (ready : BlockReady p block start)
    (hLast : 1 < last) (hStart : HighRowsFromSource p start) :
    ∃ result,
      OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result ∧ HighRowsFromSource p result := by
  obtain ⟨result, references, hRun, hReady, _, state, history⟩ := ready.copyBlock_with_history hLast
  exact ⟨result, hRun, hReady, state.high_rows_from_source history hLast hStart⟩

/-- All completed finite blocks introduce no new high row anywhere in the
mountain. Each block reconstructs its own actual map and full history. -/
theorem Preparation.blocks_high_rows
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last) (copies : Nat) :
    ∃ result,
      (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result ∧ HighRowsFromSource p result := by
  have hSizes : p.initial.size = p.reduced.size := by
    have hInitial := build_size p.initial_build
    have hReduced := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hInitial hReduced
    exact hInitial.trans hReduced.symm
  induction copies with
  | zero => exact ⟨p.reduced, rfl, p.initial_block_ready hLast,
      fun ref cell hRead _ => ⟨ref, cell, hRead, rfl⟩⟩
  | succ copies ih =>
      obtain ⟨start, hPrefix, hReady, hRows⟩ := ih
      obtain ⟨result, hCopy, hNext, hResultRows⟩ := hReady.copyBlock_with_high_rows hLast hRows
      have hStep : copyBlock start p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (copies + 1) = .ok result := by
        simpa only [hSizes] using hCopy
      exact ⟨result, forIn_yield_range_succ p.reduced
        (fun block mountain => copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)) hPrefix hStep,
        hNext, hResultRows⟩

theorem Preparation.blocks_high_rows_of_run
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    BlockReady p (copies + 1) result ∧ HighRowsFromSource p result := by
  obtain ⟨actual, hActual, hReady, hRows⟩ := p.blocks_high_rows hLast copies
  have he : actual = result := Except.ok.inj (hActual.symm.trans hRun)
  exact he ▸ ⟨hReady, hRows⟩

private theorem eventRows_of_cellAt {mountain : Mountain} {ref : Ref} {cell : Cell}
    (hRead : Canonical.cellAt mountain ref = .ok cell) (hOne : (1 : Row) ≤ cell.row) :
    cell.row ∈ (Frame.ofMountain mountain).eventRows := by
  obtain ⟨node, _, hCell⟩ := Canonical.frame_node_of_cellAt hRead
  have hRow : (Frame.ofMountain mountain).height node = cell.row := congrArg Cell.row hCell
  exact hRow ▸ Frame.height_mem_eventRows node (hRow.symm ▸ hOne)

/-- Full source-column preservation gives event-row inclusion, including
the inserted event at row one. -/
theorem PreservesColumns.eventRows_subset {before after : Mountain}
    (h : PreservesColumns before after) :
    (Frame.ofMountain before).eventRows ⊆ (Frame.ofMountain after).eventRows := by
  classical
  intro row hRow
  rcases Finset.mem_insert.mp hRow with hOne | hActual
  · exact hOne ▸ (Frame.ofMountain after).one_mem_eventRows
  · obtain ⟨hImage, hOne⟩ := Finset.mem_filter.mp hActual
    obtain ⟨node, _, hHeight⟩ := Finset.mem_image.mp hImage
    have hRead : Canonical.cellAt after (Frame.ref node) = .ok ((Frame.ofMountain before).cell node) :=
      (h.cellAt node.1.isLt).trans (Canonical.cellAt_of_frame_node before node)
    have hCellOne : (1 : Row) ≤ ((Frame.ofMountain before).cell node).row := by
      change (1 : Row) ≤ (Frame.ofMountain before).height node
      rw [hHeight]
      exact hOne
    exact hHeight ▸ eventRows_of_cellAt hRead hCellOne

/-- The global high event-row sets agree exactly with the reduced source.
The source is not the initial pre-decrement mountain. -/
theorem Preparation.blocks_high_eventRows_iff
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {row : Row} (hHigh : p.lastTop.row ≤ row) :
    row ∈ (Frame.ofMountain result).eventRows ↔ row ∈ (Frame.ofMountain p.reduced).eventRows := by
  classical
  obtain ⟨ready, hRows⟩ := p.blocks_high_rows_of_run hLast hRun
  constructor
  · intro hRow
    rcases Finset.mem_insert.mp hRow with hOne | hActual
    · exact hOne ▸ (Frame.ofMountain p.reduced).one_mem_eventRows
    · obtain ⟨hImage, hOne⟩ := Finset.mem_filter.mp hActual
      obtain ⟨node, _, hHeight⟩ := Finset.mem_image.mp hImage
      obtain ⟨sourceRef, sourceCell, hRead, hSourceRow⟩ := hRows (Frame.ref node)
        ((Frame.ofMountain result).cell node) (Canonical.cellAt_of_frame_node result node)
          (by change p.lastTop.row ≤ (Frame.ofMountain result).height node; rw [hHeight]; exact hHigh)
      have hRowEq : sourceCell.row = row := hSourceRow.trans hHeight
      exact hRowEq ▸ eventRows_of_cellAt hRead (hRowEq.symm ▸ hOne)
  · intro hRow
    exact ready.base_preserved.eventRows_subset hRow

/-- Every high event has precisely the same row membership after any
finite number of actual blocks. -/
theorem Preparation.blocks_high_eventCuts_iff
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {row : Row} (hHigh : p.lastTop.row ≤ row) :
    row ∈ (Frame.ofMountain result).eventCuts ↔ row ∈ (Frame.ofMountain p.reduced).eventCuts := by
  rw [Frame.mem_eventCuts, Frame.mem_eventCuts]
  exact p.blocks_high_eventRows_iff hLast hRun hHigh

/-- Equality of sorted high event tails, not merely a correspondence chosen
afterward. Low events may have been inserted and are filtered explicitly. -/
theorem Preparation.blocks_high_eventCuts_eq
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    (Frame.ofMountain result).eventCuts.filter (fun row => decide (p.lastTop.row ≤ row)) =
      (Frame.ofMountain p.reduced).eventCuts.filter (fun row => decide (p.lastTop.row ≤ row)) := by
  apply ((Frame.ofMountain result).eventCuts_sorted.pairwise.filter _).eq_of_mem_iff
    ((Frame.ofMountain p.reduced).eventCuts_sorted.pairwise.filter _)
  intro row
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨(p.blocks_high_eventCuts_iff hLast hRun h.2).mp h.1, h.2⟩
  · intro h
    exact ⟨(p.blocks_high_eventCuts_iff hLast hRun h.2).mpr h.1, h.2⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.DynamicBlockState.high_rows_from_source
#print axioms OmegaY.Expansion.Preparation.blocks_high_rows_of_run
#print axioms OmegaY.Expansion.Preparation.blocks_high_eventRows_iff
#print axioms OmegaY.Expansion.Preparation.blocks_high_eventCuts_eq
