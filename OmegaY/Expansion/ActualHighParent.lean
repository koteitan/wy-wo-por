/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighRows
import OmegaY.Expansion.ReducedHighTail
import OmegaY.Expansion.CopiedParentTop
import OmegaY.Expansion.BlocksTotal

/-!
# Actual parent selection above the original last top

The source parent is selected below the child's actual upper row by source
normality. Exact high-row support transfers that executable selection to a
previously copied parent column. Whole-block boundary support is derived
from actual executions, rather than supplied as a new boundary invariant.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A canonical numerical parent is the actual strict-below selector at
its child's next row. The parent may itself be a top. -/
theorem canonical_below_of_parent {mountain : Mountain}
    (hValid : MountainValid mountain) (hNormal : (Frame.ofMountain mountain).Normal)
    {child parent childUpper : (Frame.ofMountain mountain).Node}
    (hParent : (Frame.ofMountain mountain).P child = some parent)
    (hUpper : (Frame.ofMountain mountain).upper child = some childUpper) :
    below mountain parent.1.val ((Frame.ofMountain mountain).height childUpper) =
      .ok (Frame.ref parent) := by
  let F := Frame.ofMountain mountain
  have hRows : F.height childUpper = Row.B (F.height child) (F.height parent) :=
    (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
  have hLow : F.height parent < F.height childUpper := by
    rw [hRows]
    exact (Frame.P_height_le hNormal.toOrdered hParent).trans_lt (Row.lt_B _ _)
  have hColumn : mountain[parent.1.val]? = some mountain[parent.1.val] :=
    Array.getElem?_eq_getElem parent.1.isLt
  have hRead : mountain[parent.1.val][parent.2.val]? = some (F.cell parent) :=
    Array.getElem?_eq_getElem parent.2.isLt
  cases hParentUpper : F.upper parent with
  | none =>
    have hBound : F.length parent.1 ≤ parent.2.val + 1 := by
      unfold Frame.upper at hParentUpper
      split at hParentUpper
      · cases hParentUpper
      · omega
    have hIndex : parent.2.val = mountain[parent.1.val].size - 1 := by
      have hi := parent.2.isLt
      change parent.2.val < mountain[parent.1.val].size at hi
      change mountain[parent.1.val].size ≤ parent.2.val + 1 at hBound
      omega
    have hSelected := below_eq_of_top hColumn (by simpa only [← hIndex] using hRead) hLow
    simpa only [Frame.ref, hIndex] using hSelected
  | some parentUpper =>
    have hParentRow := Frame.father_upper_bound_nodes hNormal hParent hUpper hParentUpper
    have hNextRead : mountain[parent.1.val][parent.2.val + 1]? = some (F.cell parentUpper) := by
      obtain ⟨nodes, hNodes, hCell⟩ := cellAt_ok_iff.mp (cellAt_of_frame_node mountain parentUpper)
      have hSame : nodes = mountain[parent.1.val] := Option.some.inj (hNodes.symm.trans
        (by simpa only [Frame.ref, (Frame.upper_spec hParentUpper).1] using hColumn))
      simpa only [hSame, Frame.ref, (Frame.upper_spec hParentUpper).2] using hCell
    exact below_eq_of_adjacent hValid hColumn hRead hNextRead hLow hParentRow

/-- A high numerical source parent in an already copied non-root column
is selected at the unchanged source row in the actual current mountain.
No normality certificate for any copied column is a premise. -/
theorem DynamicBlockState.below_high_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent childUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hChildColumn : child.1.val = next)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hRight : p.root.column < parent.1.val)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent) :
    ∃ (ref : Ref) (cell : Cell),
      below ambient (parent.1.val + block * (p.reduced.size - 1 - p.root.column))
        ((Frame.ofMountain p.reduced).height childUpper) = .ok ref ∧
      Canonical.cellAt ambient ref = .ok cell ∧
      ref.column = parent.1.val + block * (p.reduced.size - 1 - p.root.column) ∧
      cell.row = (Frame.ofMountain p.reduced).height parent := by
  have hNormal := build_normal_of_success p.reduced_build
  have hp := (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hBefore : parent.1.val < next := by
    simpa only [hChildColumn] using Frame.P_column_lt hNormal.toOrdered hp
  obtain ⟨before, column, oldState, hRun, hPreserve, _⟩ := history.column_read hRight hBefore
  have hSourceBound : parent.1.val < p.reduced.size := hBefore.trans_le s.next_upper
  obtain ⟨d, hNoPremature, _, _⟩ := oldState.column_data hLast hSourceBound
  have hSource : p.reduced[parent.1.val]? = some d.sources :=
    (oldState.base_ambient parent.1.val hSourceBound).symm.trans d.source_column
  have hCell : d.sources[parent.2.val]? = some ((Frame.ofMountain p.reduced).cell parent) := by
    have hArray := (Array.getElem?_eq_some_iff.mp hSource).2
    rw [← hArray]
    exact Array.getElem?_eq_getElem parent.2.isLt
  have hOldBelow := canonical_below_of_parent p.reduced_valid hNormal hp hUpper
  have hBeforeBelow : below before parent.1.val ((Frame.ofMountain p.reduced).height childUpper) =
      .ok (Frame.ref parent) := (oldState.base_ambient.below hSourceBound _).trans hOldBelow
  obtain ⟨ref, cell, hBelow, hRead, hColumn, hRow⟩ :=
    d.copyColumn_below_high_source_preserved (oldState.marker_caps_below_lastTop hLast d hSourceBound)
      hNoPremature hRun hPreserve hBeforeBelow hCell hHigh
  rw [← d.destination] at hBelow hColumn
  exact ⟨ref, cell, hBelow, hRead, hColumn, hRow⟩

/-- A concrete boundary-row property used below only after deriving it
from the initial reduced build or an actual completed block. -/
def HighRootBoundary {front : List Nat} {last : Nat} (p : Preparation front last)
    (mountain : Mountain) : Prop :=
  ∃ (rootColumn boundaryColumn : Column),
    p.reduced[p.root.column]? = some rootColumn ∧
    mountain[mountain.size - 1]? = some boundaryColumn ∧
    ∀ row, p.lastTop.row ≤ row →
      (row ∈ boundaryColumn.toList.map Cell.row ↔ row ∈ rootColumn.toList.map Cell.row)

theorem Preparation.reduced_high_root_boundary {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) : HighRootBoundary p p.reduced := by
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hIndex : front.length < p.reduced.size := by omega
  have hLastIndex : p.reduced.size - 1 = front.length := by omega
  obtain ⟨rootColumn, hRootColumn, _⟩ := cellAt_ok_iff.mp p.restored_root
  let lastColumn := p.reduced[front.length]
  have hLastColumn : p.reduced[front.length]? = some lastColumn := Array.getElem?_eq_getElem hIndex
  exact ⟨rootColumn, lastColumn, hRootColumn, hLastIndex ▸ hLastColumn,
    fun _ hHigh => p.reduced_high_rows_iff hLast hLastColumn hRootColumn hHigh⟩

/-- Every actual complete block recreates the required high boundary
support, regardless of whether that property was known of its input. -/
theorem BlockReady.copyBlock_with_high_root_boundary
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start : Mountain} (ready : BlockReady p block start) (hLast : 1 < last) :
    ∃ result,
      OmegaY.Expansion.copyBlock start p.marked p.boundaries p.root.column
        (p.reduced.size - 1 - p.root.column) block = .ok result ∧
      BlockReady p (block + 1) result ∧ HighRootBoundary p result := by
  obtain ⟨result, sourceLast, copiedLast, hRun, hReady, hSource, hCopied, hRows⟩ :=
    ready.copyBlock_with_high_boundary hLast
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hIndex : p.reduced.size - 1 = front.length := by omega
  have hSourceLast : p.reduced[front.length]? = some sourceLast := by simpa only [hIndex] using hSource
  obtain ⟨rootColumn, hRootColumn, _⟩ := cellAt_ok_iff.mp p.restored_root
  exact ⟨result, hRun, hReady, rootColumn, copiedLast, hRootColumn, hCopied,
    fun row hHigh => (hRows row hHigh).trans (p.reduced_high_rows_iff hLast hSourceLast hRootColumn hHigh)⟩

/-- The actual outer block loop supplies high root-boundary support after
every finite copy count, including zero. References are still freshly
selected inside each unchanged `copyBlock` call. -/
theorem Preparation.blocks_with_high_root_boundary {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat) :
    ∃ result,
      (forIn (List.range copies) p.reduced (fun block ambient => do
        let next ← copyBlock ambient p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result ∧ HighRootBoundary p result := by
  have hSizes : p.initial.size = p.reduced.size := by
    have hi := build_size p.initial_build
    have hr := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hi hr
    exact hi.trans hr.symm
  apply forIn_range_indexed copies p.reduced _
    (fun block ambient => BlockReady p (block + 1) ambient ∧ HighRootBoundary p ambient)
  · exact ⟨p.initial_block_ready hLast, p.reduced_high_root_boundary hLast⟩
  · intro block _ ambient hState
    obtain ⟨result, hRun, hNext, hHigh⟩ := hState.1.copyBlock_with_high_root_boundary hLast
    refine ⟨result, ?_, hNext, hHigh⟩
    rw [hSizes, hRun]
    rfl

/-- An independently supplied successful outer-loop result has the same
derived boundary property, by determinism of the actual execution. -/
theorem Preparation.blocks_high_root_boundary_of_success {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block ambient => do
        let next ← copyBlock ambient p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result) :
    BlockReady p (copies + 1) result ∧ HighRootBoundary p result := by
  obtain ⟨output, hOutput, hReady, hHigh⟩ := p.blocks_with_high_root_boundary hLast copies
  have he : output = result := Except.ok.inj (hOutput.symm.trans hRun)
  exact he ▸ ⟨hReady, hHigh⟩

/-- Exact support, together with strict-below maximality in each actual
column, transfers a high selected source-root row to the boundary. This
helper is applied below only to properties derived from real block runs. -/
theorem HighRootBoundary.below_high_root {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain}
    (hBoundary : HighRootBoundary p mountain) (hValid : MountainValid mountain)
    {ceiling : Row} {sourceRef : Ref} {sourceCell : Cell}
    (hSourceBelow : below p.reduced p.root.column ceiling = .ok sourceRef)
    (hSourceRead : Canonical.cellAt p.reduced sourceRef = .ok sourceCell)
    (hHigh : p.lastTop.row ≤ sourceCell.row) :
    ∃ (ref : Ref) (cell : Cell),
      below mountain (mountain.size - 1) ceiling = .ok ref ∧
      Canonical.cellAt mountain ref = .ok cell ∧
      ref.column = mountain.size - 1 ∧ cell.row = sourceCell.row := by
  obtain ⟨rootColumn, boundaryColumn, hRootColumn, hBoundaryColumn, hRows⟩ := hBoundary
  obtain ⟨hSourceColumn, selected, hSelected, hSelectedBelow⟩ := below_result hRootColumn hSourceBelow
  have hSelectedRead : Canonical.cellAt p.reduced sourceRef = .ok selected :=
    cellAt_ok_iff.mpr ⟨rootColumn, by simpa only [hSourceColumn] using hRootColumn, hSelected⟩
  have he : selected = sourceCell := Except.ok.inj (hSelectedRead.symm.trans hSourceRead)
  subst selected
  have hSourceMem : sourceCell.row ∈ rootColumn.toList.map Cell.row :=
    List.mem_map.mpr ⟨sourceCell, List.mem_of_getElem?
      (by simpa only [Array.getElem?_toList] using hSelected), rfl⟩
  obtain ⟨floorCell, hFloorMem, hFloorRow⟩ := List.mem_map.mp ((hRows _ hHigh).mpr hSourceMem)
  obtain ⟨floorIndex, hFloorIndex⟩ := List.mem_iff_getElem?.mp hFloorMem
  have hFloorRead : Canonical.cellAt mountain ⟨mountain.size - 1, floorIndex⟩ = .ok floorCell :=
    cellAt_ok_iff.mpr ⟨boundaryColumn, hBoundaryColumn,
      by simpa only [Array.getElem?_toList] using hFloorIndex⟩
  obtain ⟨ref, cell, hBelow, hRead, hColumn, hFloorLe, hBelowCeiling⟩ :=
    below_between hValid hFloorRead (by simpa only [hFloorRow] using hSelectedBelow)
  have hSourceLe : sourceCell.row ≤ cell.row := by simpa only [hFloorRow] using hFloorLe
  obtain ⟨nodes, hNodes, hCellRead⟩ := cellAt_ok_iff.mp hRead
  have heNodes : nodes = boundaryColumn := Option.some.inj
    (hNodes.symm.trans (by simpa only [hColumn] using hBoundaryColumn))
  subst nodes
  have hCellMem : cell.row ∈ boundaryColumn.toList.map Cell.row :=
    List.mem_map.mpr ⟨cell, List.mem_of_getElem?
      (by simpa only [Array.getElem?_toList] using hCellRead), rfl⟩
  obtain ⟨oldCell, hOldMem, hOldRow⟩ := List.mem_map.mp ((hRows _ (hHigh.trans hSourceLe)).mp hCellMem)
  obtain ⟨oldIndex, hOldIndex⟩ := List.mem_iff_getElem?.mp hOldMem
  obtain ⟨hc, hRootEq⟩ := Array.getElem?_eq_some_iff.mp hRootColumn
  have hCV : ColumnValid p.reduced p.root.column rootColumn := hRootEq ▸ p.reduced_valid _ hc
  have hStrict : StrictMono (fun i : Fin rootColumn.size => rootColumn[i.val].row) := by
    intro i j hij
    exact hCV.rows_strict _ _ _ _ (Array.getElem?_eq_getElem i.isLt)
      (Array.getElem?_eq_getElem j.isLt) hij
  have hAtMost := below_max_row hRootColumn hStrict hSourceBelow hSelected
    (show rootColumn[oldIndex]? = some oldCell by simpa only [Array.getElem?_toList] using hOldIndex)
    (show oldCell.row < ceiling by simpa only [hOldRow] using hBelowCeiling)
  have hCellLe : cell.row ≤ sourceCell.row := by simpa only [hOldRow] using hAtMost
  exact ⟨ref, cell, hBelow, hRead, hColumn, le_antisymm hCellLe hSourceLe⟩

/-- The actual block boundary after any finite outer-loop prefix selects
a high numerical root-column parent at its source height. The boundary
support certificate is a conclusion of that loop, not an input. -/
theorem Preparation.blocks_boundary_below_high_parent {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (copies : Nat)
    {child parent childUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hParentColumn : parent.1.val = p.root.column)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent) :
    ∃ result ref cell,
      (forIn (List.range copies) p.reduced (fun block ambient => do
        let next ← copyBlock ambient p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok result ∧
      BlockReady p (copies + 1) result ∧
      below result (result.size - 1) ((Frame.ofMountain p.reduced).height childUpper) = .ok ref ∧
      Canonical.cellAt result ref = .ok cell ∧ ref.column = result.size - 1 ∧
      cell.row = (Frame.ofMountain p.reduced).height parent := by
  obtain ⟨result, hRun, hReady, hBoundary⟩ := p.blocks_with_high_root_boundary hLast copies
  have hNormal := build_normal_of_success p.reduced_build
  have hp := (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hSourceBelow := canonical_below_of_parent p.reduced_valid hNormal hp hUpper
  rw [hParentColumn] at hSourceBelow
  obtain ⟨ref, cell, hBelow, hRead, hColumn, hRow⟩ :=
    hBoundary.below_high_root hReady.valid hSourceBelow (cellAt_of_frame_node p.reduced parent) hHigh
  exact ⟨result, ref, cell, hRun, hReady, hBelow, hRead, hColumn, hRow⟩

/-- At a current inner-loop state, an actual outer-loop prefix supplies
the high boundary certificate. Preservation into the current ambient
mountain gives the exact selector in the shifted root column. -/
theorem DynamicBlockState.below_high_root_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    {child parent childUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : findParent p.reduced (Frame.ref child) = .ok (Frame.ref parent))
    (hUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hParentColumn : parent.1.val = p.root.column)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height parent) :
    ∃ (ref : Ref) (cell : Cell),
      below ambient (p.root.column + block * (p.reduced.size - 1 - p.root.column))
        ((Frame.ofMountain p.reduced).height childUpper) = .ok ref ∧
      Canonical.cellAt ambient ref = .ok cell ∧
      ref.column = p.root.column + block * (p.reduced.size - 1 - p.root.column) ∧
      cell.row = (Frame.ofMountain p.reduced).height parent := by
  have hBoundary := (p.blocks_high_root_boundary_of_success hLast hStartRun).2
  have hNormal := build_normal_of_success p.reduced_build
  have hp := (Executable.findParent_ref_iff hNormal.toOrdered child parent).mp hParent
  have hSourceBelow := canonical_below_of_parent p.reduced_valid hNormal hp hUpper
  rw [hParentColumn] at hSourceBelow
  obtain ⟨ref, cell, hBelow, hRead, hColumn, hRow⟩ :=
    hBoundary.below_high_root s.start_valid hSourceBelow (cellAt_of_frame_node p.reduced parent) hHigh
  obtain ⟨nodes, hNodes, hIndex⟩ := cellAt_ok_iff.mp hRead
  have hStartBound : start.size - 1 < start.size := by
    have hb := (Array.getElem?_eq_some_iff.mp hNodes).1
    simpa only [hColumn] using hb
  have hActualBelow := (s.start_preserved.below hStartBound _).trans hBelow
  have hActualRead : Canonical.cellAt ambient ref = .ok cell :=
    cellAt_ok_iff.mpr ⟨nodes, s.start_preserved.column_read hNodes, hIndex⟩
  have hBoundaryIndex : start.size - 1 =
      p.root.column + block * (p.reduced.size - 1 - p.root.column) := by
    have hs := s.start_size
    omega
  rw [hBoundaryIndex] at hActualBelow hColumn
  exact ⟨ref, cell, hActualBelow, hActualRead, hColumn, hRow⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.canonical_below_of_parent
#print axioms OmegaY.Expansion.DynamicBlockState.below_high_parent
#print axioms OmegaY.Expansion.Preparation.reduced_high_root_boundary
#print axioms OmegaY.Expansion.BlockReady.copyBlock_with_high_root_boundary
#print axioms OmegaY.Expansion.Preparation.blocks_with_high_root_boundary
#print axioms OmegaY.Expansion.Preparation.blocks_high_root_boundary_of_success
#print axioms OmegaY.Expansion.HighRootBoundary.below_high_root
#print axioms OmegaY.Expansion.Preparation.blocks_boundary_below_high_parent
#print axioms OmegaY.Expansion.DynamicBlockState.below_high_root_parent
