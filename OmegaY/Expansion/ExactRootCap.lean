/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ExactRootCap.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualRootInterval

/-! Retain the membership of an interval ceiling in the actual boundary
list. ActualRootInterval deliberately contains sufficient local geometry;
its type alone does not say that an arbitrary degree is this exact cap. -/

namespace OmegaY.Expansion

open Canonical Geometry

theorem Preparation.boundary_member_cases {front : List Nat} {last : Nat}
    (p : Preparation front last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes) {row : Row} (hRow : row ∈ p.boundaries) :
    row = p.lastTop.row ∨ ∃ i cell, i ≤ p.root.index ∧ nodes[i]? = some cell ∧ cell.row = row := by
  rw [p.boundaries_of_column hColumn] at hRow
  rcases List.mem_cons.mp hRow with hTop | hRows
  · exact Or.inl hTop
  · obtain ⟨cell, hMem, hFilter⟩ := List.mem_filterMap.mp hRows
    have hCellRow : cell.row = row := by
      by_cases hz : cell.row = 0
      · simp only [hz, ↓reduceIte, reduceCtorEq] at hFilter
      · simpa only [hz, ↓reduceIte, Option.some.injEq] using hFilter
    obtain ⟨i, hi, hCell⟩ := List.mem_take_iff_getElem.mp (List.mem_reverse.mp hMem)
    have hRead : nodes[i]? = some cell := by
      have hList : nodes.toList[i]? = some cell := List.getElem?_eq_some_iff.mpr ⟨by omega, hCell⟩
      simpa only [Array.getElem?_toList] using hList
    exact Or.inr ⟨i, cell, by omega, hRead, hCellRow⟩

/-- A boundary above a root-prefix node and below its next root row is
that next root row. No intermediate rows are postulated. -/
theorem Preparation.boundary_cap_eq_next {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes) {i : Nat} {lower upper : Cell}
    (hLower : nodes[i]? = some lower) (hUpper : nodes[i + 1]? = some upper)
    (hIndex : i < p.root.index) {cap : Row} (hMem : cap ∈ p.boundaries)
    (hLow : lower.row < cap) (hHigh : cap ≤ upper.row) : cap = upper.row := by
  apply le_antisymm hHigh
  rcases p.boundary_member_cases hColumn hMem with hTop | ⟨j, cell, _, hRead, hRow⟩
  · rw [hTop]
    exact (p.root_prefix_row_le hColumn hUpper (by omega)).trans (p.root_row_lt_top hLast).le
  · obtain ⟨hc, hNodes⟩ := Array.getElem?_eq_some_iff.mp hColumn
    have hValid : ColumnValid p.initial p.root.column nodes := hNodes ▸ p.initial_valid _ hc
    have hAfter : i < j := by
      by_contra hn
      rcases eq_or_lt_of_le (Nat.le_of_not_gt hn) with he | hl
      · have hSame : cell = lower := Option.some.inj (hRead.symm.trans (by simpa only [he] using hLower))
        exact (ne_of_lt hLow) ((congrArg Cell.row hSame).symm.trans hRow)
      · have hLt := hValid.rows_strict _ _ _ _ hRead hLower hl
        exact (not_lt_of_ge hLow.le) (hRow ▸ hLt)
    rcases eq_or_lt_of_le (show i + 1 ≤ j by omega) with he | hl
    · have hSame : upper = cell := Option.some.inj (hUpper.symm.trans (by simpa only [he] using hRead))
      exact (congrArg Cell.row hSame).trans hRow |>.le
    · exact (hValid.rows_strict _ _ _ _ hUpper hRead hl).le.trans (le_of_eq hRow)

theorem Preparation.boundary_cap_eq_lastTop {front : List Nat} {last : Nat}
    (p : Preparation front last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes) {cap : Row}
    (hMem : cap ∈ p.boundaries) (hLow : p.rootCell.row < cap) : cap = p.lastTop.row := by
  rcases p.boundary_member_cases hColumn hMem with hTop | ⟨i, cell, hi, hRead, hRow⟩
  · exact hTop
  · have hBelow := p.root_prefix_row_le hColumn hRead hi
    exact False.elim ((not_lt_of_ge (hRow ▸ hBelow)) hLow)

/-- An arbitrary current boundary supplies an interval together with its
literal ceiling membership. Unlike a general local interval certificate,
this result retains the actual root-boundary partition used to select it. -/
theorem RootRowsInColumn.root_interval_with_boundary {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {column : Nat}
    (hRows : RootRowsInColumn p mountain column) (hValid : MountainValid mountain)
    (hLast : 1 < last) {nodes : Column}
    (hColumn : p.initial[p.root.column]? = some nodes) {index : Nat} {lower : Cell}
    (hLower : nodes[index]? = some lower) (hIndex : index ≤ p.root.index)
    {references : List Ref} (hMap : p.boundaries.mapM (below mountain column) = .ok references) :
    ∃ ceiling degree ref cell, ceiling ∈ p.boundaries ∧
      ceiling = Row.bump lower.row degree ∧ ceiling ≤ p.lastTop.row ∧
      below mountain column ceiling = .ok ref ∧ Canonical.cellAt mountain ref = .ok cell ∧
      ref.column = column ∧ referenceAt mountain references lower.row = .ok cell.row ∧
      lower.row ≤ cell.row ∧ cell.row < ceiling ∧
      ∀ higherIndex higherCell, index < higherIndex → higherIndex ≤ p.root.index →
        nodes[higherIndex]? = some higherCell → ceiling ≤ higherCell.row := by
  obtain ⟨earlier, ceiling, later, degree, hPartition, hPower, hTop, hLater, hHigher⟩ :=
    p.root_boundary_partition hLast hColumn hLower hIndex
  obtain ⟨floorRef, floorCell, hFloor, hFloorColumn, hFloorRow⟩ := hRows hColumn hLower hIndex
  have hBelow : floorCell.row < ceiling := by rw [hFloorRow, hPower]; exact Row.lt_bump _ _
  obtain ⟨ref, cell, hSelected, hRead, hRefColumn, hAbove, hUpper⟩ := below_between hValid hFloor hBelow
  rw [hFloorColumn] at hSelected hRefColumn
  rw [hFloorRow] at hAbove
  have hReference := referenceAt_of_boundary_partition
    (Array.getElem?_eq_getElem hRows.column_lt) hPartition hMap hSelected
    (lookup_ok_iff.mpr (cellAt_ok_iff.mp hRead)) hAbove hLater
  exact ⟨ceiling, degree, ref, cell, by rw [hPartition]; simp, hPower, hTop, hSelected,
    hRead, hRefColumn, hReference, hAbove, hUpper, hHigher⟩

/-- Replace a sufficient interval certificate by one whose cap retains
its actual partition origin. The source root and queried target row are
unchanged; no uniqueness of an arbitrary certificate's degree is assumed. -/
theorem DynamicBlockState.with_exact_root_cap {front : List Nat} {last : Nat}
    {p : Preparation front last} {block : Nat} {start ambient : Mountain}
    {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow) :
    ∃ b : ActualRootInterval p start ambient references rootIndex rootRow,
      b.root = a.root ∧ b.target.row = a.target.row ∧ Row.bump rootRow b.degree ∈ p.boundaries := by
  have hReducedRead : Canonical.cellAt p.reduced ⟨p.root.column, rootIndex⟩ =
      .ok ((Frame.ofMountain p.reduced).cell a.root) := by
    simpa only [a.root_ref] using cellAt_of_frame_node p.reduced a.root
  have hInitialRead : Canonical.cellAt p.initial ⟨p.root.column, rootIndex⟩ =
      .ok ((Frame.ofMountain p.reduced).cell a.root) :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, rootIndex⟩)
      p.initial_build p.reduced_build p.root_before_last).trans hReducedRead
  obtain ⟨nodes, hColumn, hSource⟩ := cellAt_ok_iff.mp hInitialRead
  obtain ⟨ceiling, degree, ref, target, hMem, hPower, hTop, hBelow, hRead, hRefColumn,
      hQuery, hLow, hHigh, hHigher⟩ := RootRowsInColumn.root_interval_with_boundary
    s.boundary_rows s.start_valid hLast hColumn hSource a.root_prefix s.reference_map
  have hPower' : ceiling = Row.bump rootRow degree := by
    simpa only [← a.root_row, Frame.height] using hPower
  have hLow' : rootRow ≤ target.row := by simpa only [← a.root_row, Frame.height] using hLow
  have hQuery' : referenceAt start references rootRow = .ok target.row := by
    simpa only [← a.root_row, Frame.height] using hQuery
  have hTargetEq : target.row = a.target.row := Except.ok.inj (hQuery'.symm.trans a.start_query)
  obtain ⟨targetNodes, hTargetNodes, hTargetIndex⟩ := cellAt_ok_iff.mp hRead
  have hAmbientRead : Canonical.cellAt ambient ref = .ok target :=
    cellAt_ok_iff.mpr ⟨targetNodes, s.start_preserved.column_read hTargetNodes, hTargetIndex⟩
  have hBarrier := p.root_prefix_upper_barrier hLast hColumn a.root_prefix hTop hHigher a.root_ref
  have hRaised : rootRow < target.row → 0 < degree := by
    intro hStrict
    by_contra hn
    have hd : degree = 0 := by omega
    have hHighZero : target.row < Row.bump rootRow 0 := by simpa only [hPower', hd] using hHigh
    have hEq : rootRow = target.row := Row.jump_eq_zero.mp
      (Nat.eq_zero_of_le_zero (Row.jump_le_of_lt_bump hLow' hHighZero))
    exact (ne_of_lt hStrict) hEq
  let b : ActualRootInterval p start ambient references rootIndex rootRow := {
    a with
    degree := degree
    reference := ref
    target := target
    reference_column := hRefColumn
    target_start_read := hRead
    target_ambient_read := hAmbientRead
    start_query := hQuery'
    ambient_query := (s.referenceAt_preserved rootRow).trans hQuery'
    start_below := by simpa only [hPower'] using hBelow
    ambient_below := by simpa only [hPower'] using
      (s.start_preserved.below (RootRowsInColumn.column_lt s.boundary_rows) ceiling).trans hBelow
    target_lower := hLow'
    target_below := by simpa only [hPower'] using hHigh
    cap_top := by simpa only [hPower'] using hTop
    higher_prefix_barrier := by
      intro otherNodes higherIndex higherCell hOtherColumn hBefore hPrefix hHigherRead
      have he : otherNodes = nodes := Option.some.inj (hOtherColumn.symm.trans hColumn)
      subst otherNodes
      simpa only [hPower'] using hHigher higherIndex higherCell hBefore hPrefix hHigherRead
    root_upper_barrier := by simpa only [hPower'] using hBarrier
    raised_degree := hRaised }
  exact ⟨b, rfl, hTargetEq, by simpa only [b, hPower'] using hMem⟩

/-- Below the bad root, the exact cap is the source root's next row. -/
theorem ActualRootInterval.cap_eq_upper_of_boundary
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    (hLast : 1 < last) (hMem : Row.bump rootRow a.degree ∈ p.boundaries)
    (hBefore : rootIndex < p.root.index)
    {upper : (Frame.ofMountain p.reduced).Node}
    (hUpper : (Frame.ofMountain p.reduced).upper a.root = some upper) :
    Row.bump rootRow a.degree = (Frame.ofMountain p.reduced).height upper := by
  have hUpperRef : Frame.ref upper = ⟨p.root.column, rootIndex + 1⟩ := by
    have hSpec := Frame.upper_spec hUpper
    have hr := a.root_ref
    simp only [Frame.ref, Ref.mk.injEq] at hr ⊢
    exact ⟨(congrArg Fin.val hSpec.1).trans hr.1, hSpec.2.trans (congrArg (· + 1) hr.2)⟩
  have hRootRead : Canonical.cellAt p.initial ⟨p.root.column, rootIndex⟩ =
      .ok ((Frame.ofMountain p.reduced).cell a.root) :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, rootIndex⟩)
      p.initial_build p.reduced_build p.root_before_last).trans
      (by simpa only [a.root_ref] using cellAt_of_frame_node p.reduced a.root)
  have hAboveRead : Canonical.cellAt p.initial ⟨p.root.column, rootIndex + 1⟩ =
      .ok ((Frame.ofMountain p.reduced).cell upper) :=
    (build_changed_last_preserves_ref (ref := ⟨p.root.column, rootIndex + 1⟩)
      p.initial_build p.reduced_build p.root_before_last).trans
      (by simpa only [hUpperRef] using cellAt_of_frame_node p.reduced upper)
  obtain ⟨nodes, hColumn, hLowRead⟩ := cellAt_ok_iff.mp hRootRead
  obtain ⟨aboveNodes, hAboveColumn, hHighRead⟩ := cellAt_ok_iff.mp hAboveRead
  have hNodes : aboveNodes = nodes := Option.some.inj (hAboveColumn.symm.trans hColumn)
  subst aboveNodes
  exact p.boundary_cap_eq_next hLast hColumn hLowRead hHighRead hBefore hMem
    (by change (Frame.ofMountain p.reduced).height a.root < _; rw [a.root_row]; exact Row.lt_bump _ _)
    (a.root_upper_barrier upper hUpper)

/-- At the bad root itself, the exact cap is the old final top. -/
theorem ActualRootInterval.cap_eq_lastTop_of_boundary
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {start ambient : Mountain} {references : List Ref} {rootIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references rootIndex rootRow)
    (hMem : Row.bump rootRow a.degree ∈ p.boundaries) (hAtEnd : rootIndex = p.root.index) :
    Row.bump rootRow a.degree = p.lastTop.row := by
  have hRootRef : Frame.ref a.root = p.root := by simpa only [hAtEnd] using a.root_ref
  have hRead : Canonical.cellAt p.reduced p.root = .ok ((Frame.ofMountain p.reduced).cell a.root) := by
    simpa only [hRootRef] using cellAt_of_frame_node p.reduced a.root
  have hCell : (Frame.ofMountain p.reduced).cell a.root = p.rootCell :=
    Except.ok.inj (hRead.symm.trans p.restored_root)
  have hRow : p.rootCell.row = rootRow := (congrArg Cell.row hCell).symm.trans a.root_row
  obtain ⟨nodes, hColumn, _⟩ := cellAt_ok_iff.mp p.initial_root
  exact p.boundary_cap_eq_lastTop hColumn hMem (hRow ▸ Row.lt_bump rootRow a.degree)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.boundary_member_cases
#print axioms OmegaY.Expansion.Preparation.boundary_cap_eq_next
#print axioms OmegaY.Expansion.Preparation.boundary_cap_eq_lastTop
#print axioms OmegaY.Expansion.RootRowsInColumn.root_interval_with_boundary
#print axioms OmegaY.Expansion.DynamicBlockState.with_exact_root_cap
#print axioms OmegaY.Expansion.ActualRootInterval.cap_eq_upper_of_boundary
#print axioms OmegaY.Expansion.ActualRootInterval.cap_eq_lastTop_of_boundary
