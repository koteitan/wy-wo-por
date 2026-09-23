/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawFatherBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawFrontier
import OmegaY.Expansion.FillAdjacent
import OmegaY.Expansion.ActualIntervalEdge

/-!
# Upper barriers for actual copied stored fathers

The selector's last eligible index forces its actual successor to be at least
the query row. Reference filling has the same bound from its actual ladder
endpoints. These are statements about stored references and successful reads;
no numerical parent identification or normality of copied columns is assumed.

The fixed-endpoint copy branch is exposed separately: successful copying alone
does not bound an arbitrary requested row by a fixed father's successor.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- The upper-stored endpoint obeys its actual father's next-row barrier. -/
def CellRawFatherBound (mountain : Mountain) (cell : Cell) : Prop :=
  ∀ ref parentUpper, cell.left = some ref →
    Canonical.cellAt mountain ⟨ref.column, ref.index + 1⟩ = .ok parentUpper →
    cell.row ≤ parentUpper.row

/-- Index maximality alone proves this; strict row order is unnecessary. -/
theorem below_parent_upper_bound {mountain : Mountain} {column : Nat} {nodes : Column}
    (hColumn : mountain[column]? = some nodes) {query : Row} {parentRef : Ref}
    (hBelow : below mountain column query = .ok parentRef) {parentUpper : Cell}
    (hUpper : nodes[parentRef.index + 1]? = some parentUpper) :
    query ≤ parentUpper.row := by
  by_contra h
  have hIndex := below_max_index hColumn hBelow hUpper (lt_of_not_ge h)
  omega

theorem below_parent_upper_bound_at {mountain : Mountain} {column : Nat}
    {query : Row} {parentRef : Ref}
    (hBelow : below mountain column query = .ok parentRef) {parentUpper : Cell}
    (hUpper : Canonical.cellAt mountain ⟨parentRef.column, parentRef.index + 1⟩ =
      .ok parentUpper) : query ≤ parentUpper.row := by
  cases hColumn : mountain[column]? with
  | none => simp [below, columnAt, hColumn] at hBelow
  | some nodes =>
    have hRefColumn := (below_result hColumn hBelow).1
    obtain ⟨upperNodes, hUpperColumn, hUpperIndex⟩ := cellAt_ok_iff.mp hUpper
    simp only [hRefColumn] at hUpperColumn
    have hNodes : upperNodes = nodes := Option.some.inj (hUpperColumn.symm.trans hColumn)
    subst upperNodes
    exact below_parent_upper_bound hColumn hBelow hUpperIndex

theorem CellRawFatherBound.of_below {mountain : Mountain} {column : Nat}
    {cell : Cell} {parentRef : Ref}
    (hLeft : cell.left = some parentRef)
    (hBelow : below mountain column cell.row = .ok parentRef) :
    CellRawFatherBound mountain cell := by
  intro ref parentUpper hStored hUpper
  have hRef : ref = parentRef := Option.some.inj (hStored.symm.trans hLeft)
  subst ref
  exact below_parent_upper_bound_at hBelow hUpper

/-- Numerical backfill preserves exactly the fields relevant to this bound. -/
theorem CellRawFatherBound.sameShape {mountain : Mountain} {original output : Cell}
    (hBound : CellRawFatherBound mountain original) (hShape : SameShape original output) :
    CellRawFatherBound mountain output := by
  intro ref parentUpper hLeft hUpper
  rw [← hShape.1]
  exact hBound ref parentUpper (hShape.2.trans hLeft) hUpper

/-- Complete old columns retain every possible upper successor as well as
the selected endpoint. The domain bound is only on the stored parent column. -/
theorem CellRawFatherBound.preserve {before after : Mountain} {cell : Cell}
    (hBound : CellRawFatherBound before cell) (hPreserve : PreservesColumns before after)
    (hOld : ∀ ref, cell.left = some ref → ref.column < before.size) :
    CellRawFatherBound after cell := by
  intro ref parentUpper hLeft hUpper
  apply hBound ref parentUpper hLeft
  exact (hPreserve.cellAt (ref := ⟨ref.column, ref.index + 1⟩)
    (show ref.column < before.size from hOld ref hLeft)).symm.trans hUpper

theorem CellRawFatherBound.push {mountain : Mountain} {cell : Cell}
    (hBound : CellRawFatherBound mountain cell) (column : Column)
    (hOld : ∀ ref, cell.left = some ref → ref.column < mountain.size) :
    CellRawFatherBound (mountain.push column) cell :=
  hBound.preserve (PreservesColumns.push mountain column) hOld

/-- The actual run exposes the program's endpoint branch. In particular the
moved branch retains the exact successful selector call, not just its row. -/
theorem copyEdge_parent_cases {mountain : Mountain} {source : Ref}
    {shift rootColumn : Nat} {row : Row} {copied : Cell} {parentRef : Ref}
    (hRun : copyEdge mountain source shift rootColumn row = .ok copied)
    (hStored : copied.left = some parentRef) :
    ∃ sourceCell oldParent, lookup mountain source = .ok sourceCell ∧
      sourceCell.row ≠ 0 ∧ sourceCell.left = some oldParent ∧
      parentRef.column < source.column + shift ∧
      ((oldParent.column < rootColumn ∧ parentRef = oldParent) ∨
       (rootColumn ≤ oldParent.column ∧
        below mountain (oldParent.column + shift) row = .ok parentRef)) := by
  cases hSource : lookup mountain source with
  | error error => simp [copyEdge, hSource] at hRun
  | ok sourceCell =>
    by_cases hZero : sourceCell.row = 0
    · have he : (⟨row, 0, none⟩ : Cell) = copied := by
        simpa [copyEdge, hSource, hZero] using hRun
      rw [← he] at hStored
      cases hStored
    · cases hLeft : sourceCell.left with
      | none => simp [copyEdge, hSource, hZero, leftOf, hLeft] at hRun
      | some oldParent =>
        by_cases hFixed : oldParent.column < rootColumn
        · by_cases hDestination : oldParent.column < source.column + shift
          · have he : (⟨row, 0, some oldParent⟩ : Cell) = copied := by
              simpa [copyEdge, hSource, hZero, leftOf, hLeft, hFixed,
                Nat.not_le_of_gt hDestination] using hRun
            have hRef : oldParent = parentRef := Option.some.inj (by simpa only [← he] using hStored)
            exact ⟨sourceCell, oldParent, rfl, hZero, hLeft,
              hRef ▸ hDestination, Or.inl ⟨hFixed, hRef.symm⟩⟩
          · simp [copyEdge, hSource, hZero, leftOf, hLeft, hFixed,
              Nat.le_of_not_gt hDestination] at hRun
        · cases hBelow : below mountain (oldParent.column + shift) row with
          | error error =>
            simp [copyEdge, hSource, hZero, leftOf, hLeft, hFixed, hBelow] at hRun
          | ok parent =>
            by_cases hDestination : parent.column < source.column + shift
            · have he : (⟨row, 0, some parent⟩ : Cell) = copied := by
                simpa [copyEdge, hSource, hZero, leftOf, hLeft, hFixed, hBelow,
                  Nat.not_le_of_gt hDestination] using hRun
              have hRef : parent = parentRef := Option.some.inj (by simpa only [← he] using hStored)
              exact ⟨sourceCell, oldParent, rfl, hZero, hLeft,
                hRef ▸ hDestination, Or.inr ⟨Nat.le_of_not_gt hFixed, hRef ▸ hBelow⟩⟩
            · simp [copyEdge, hSource, hZero, leftOf, hLeft, hFixed, hBelow,
                Nat.le_of_not_gt hDestination] at hRun

/-- Every real moved endpoint of an actual copy obeys raw D automatically. -/
theorem copyEdge_moved_rawFatherBound {mountain : Mountain} {source : Ref}
    {shift rootColumn : Nat} {row : Row} {copied sourceCell : Cell} {oldParent : Ref}
    (hRun : copyEdge mountain source shift rootColumn row = .ok copied)
    (hSource : lookup mountain source = .ok sourceCell)
    (hSourceLeft : sourceCell.left = some oldParent)
    (hMoved : rootColumn ≤ oldParent.column) : CellRawFatherBound mountain copied := by
  intro ref parentUpper hLeft hUpper
  obtain ⟨actualSource, actualParent, hActualSource, _, hActualLeft, _, hCases⟩ :=
    copyEdge_parent_cases hRun hLeft
  have hSourceEq : actualSource = sourceCell := Except.ok.inj (hActualSource.symm.trans hSource)
  subst actualSource
  have hParentEq : actualParent = oldParent := Option.some.inj (hActualLeft.symm.trans hSourceLeft)
  subst actualParent
  rcases hCases with ⟨hFixed, _⟩ | ⟨_, hBelow⟩
  · omega
  · rw [copyEdge_return_row hRun]
    exact below_parent_upper_bound_at hBelow hUpper

/-- A fill rung is at most the actual successor of its own stored parent. -/
theorem fillCells_rawFatherBound {mountain : Mountain} {nodes : Column} {column : Nat}
    (hColumn : mountain[column]? = some nodes) (hStrict : FillRowsStrict nodes)
    {capIndex : Nat} {cap : Cell} {low high : Row} {cell : Cell}
    (hCap : nodes[capIndex]? = some cap) (hHigh : high ≤ cap.row)
    (hMem : cell ∈ fillCells nodes column low high) : CellRawFatherBound mountain cell := by
  obtain ⟨index, parent, upper, _, hUpper, _, _, hRows, _, hLadder, _, hLeft⟩ :=
    mem_fillCells hStrict hCap hHigh hMem
  intro ref parentUpper hStored hUpperRead
  have hRef : ref = ⟨column, index⟩ := Option.some.inj (hStored.symm.trans hLeft)
  subst ref
  have hRead : Canonical.cellAt mountain ⟨column, index + 1⟩ = .ok upper :=
    cellAt_ok_iff.mpr ⟨nodes, hColumn, hUpper⟩
  have hEq : parentUpper = upper := Except.ok.inj (hUpperRead.symm.trans hRead)
  subst parentUpper
  exact (Row.fillLadder_bounds hRows hLadder).2

theorem fillCellsAscending_rawFatherBound {mountain : Mountain} {nodes : Column} {column : Nat}
    (hColumn : mountain[column]? = some nodes) (hStrict : FillRowsStrict nodes)
    {capIndex : Nat} {cap : Cell} {low high : Row} {cell : Cell}
    (hCap : nodes[capIndex]? = some cap) (hHigh : high ≤ cap.row)
    (hMem : cell ∈ fillCellsAscending nodes column low high) :
    CellRawFatherBound mountain cell :=
  fillCells_rawFatherBound hColumn hStrict hCap hHigh
    ((fillCellsAscending_perm nodes column low high).mem_iff.mp hMem)

/-- The cell certificate targets precisely the typed stored-parent bound. -/
theorem rawFatherUpperBound_of_cells {mountain : Mountain}
    (hCells : ∀ (u upper : (Frame.ofMountain mountain).Node), Frame.Real u →
      (Frame.ofMountain mountain).upper u = some upper →
      CellRawFatherBound mountain ((Frame.ofMountain mountain).cell upper)) :
    (Frame.ofMountain mountain).RawFatherUpperBound := by
  intro u parent upper parentUpper hReal hParent hUpper hParentUpper
  obtain ⟨actualUpper, hActualUpper, hLeft⟩ := Frame.rawParent_spec hParent
  have hEq : actualUpper = upper := Option.some.inj (hActualUpper.symm.trans hUpper)
  subst actualUpper
  have hSpec := Frame.upper_spec hParentUpper
  have hRef : Frame.ref parentUpper = ⟨parent.1.val, parent.2.val + 1⟩ := by
    simp only [Frame.ref, hSpec.1, hSpec.2]
  apply hCells u upper hReal hUpper (Frame.ref parent)
    ((Frame.ofMountain mountain).cell parentUpper) hLeft
  change Canonical.cellAt mountain ⟨parent.1.val, parent.2.val + 1⟩ = _
  rw [← hRef]
  exact Canonical.cellAt_of_frame_node mountain parentUpper

end OmegaY.Expansion

#print axioms OmegaY.Expansion.below_parent_upper_bound_at
#print axioms OmegaY.Expansion.CellRawFatherBound.preserve
#print axioms OmegaY.Expansion.copyEdge_parent_cases
#print axioms OmegaY.Expansion.copyEdge_moved_rawFatherBound
#print axioms OmegaY.Expansion.fillCells_rawFatherBound
#print axioms OmegaY.Expansion.fillCellsAscending_rawFatherBound
#print axioms OmegaY.Expansion.rawFatherUpperBound_of_cells
