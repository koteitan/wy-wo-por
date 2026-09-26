/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BadRootHighQuery.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighParent
import OmegaY.Expansion.ActualRootInterval

/-!
# High queries whose source father is exactly the bad root

The real boundary has the source root's high-row support. A high boundary
row strictly below the query would therefore be a source root-column row
above its selected source father, contradicting source strict-below
maximality. Thus raising the query above the old last top introduces no
new eligible boundary node. The source selector already covers both the
case with a father upper and the case where the father is a top.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A low source-root selection forbids any new high candidate in the
boundary. The actual selector at the old last top remains unchanged at
the larger query. No density or upper-neighbour assumption is needed. -/
theorem HighRootBoundary.below_query_of_low_source
    {front : List Nat} {last : Nat} {p : Preparation front last} {mountain : Mountain}
    (hBoundary : HighRootBoundary p mountain) {query : Row} {sourceRef : Ref} {sourceCell : Cell}
    (hSourceBelow : below p.reduced p.root.column query = .ok sourceRef)
    (hSourceRead : Canonical.cellAt p.reduced sourceRef = .ok sourceCell)
    (hSourceLow : sourceCell.row < p.lastTop.row)
    {targetRef : Ref} {target : Cell}
    (hAtTop : below mountain (mountain.size - 1) p.lastTop.row = .ok targetRef)
    (hTargetRead : Canonical.cellAt mountain targetRef = .ok target)
    (hQueryHigh : p.lastTop.row ≤ query) :
    below mountain (mountain.size - 1) query = .ok targetRef := by
  obtain ⟨rootColumn, boundaryColumn, hRootColumn, hBoundaryColumn, hRows⟩ := hBoundary
  obtain ⟨hSourceColumn, selectedSource, hSelectedSource, _⟩ := below_result hRootColumn hSourceBelow
  have hSelectedRead : Canonical.cellAt p.reduced sourceRef = .ok selectedSource :=
    cellAt_ok_iff.mpr ⟨rootColumn, by simpa only [hSourceColumn] using hRootColumn, hSelectedSource⟩
  have hSourceEq : selectedSource = sourceCell := Except.ok.inj (hSelectedRead.symm.trans hSourceRead)
  subst selectedSource
  obtain ⟨hTargetColumn, selectedTarget, hSelectedTarget, hTargetBelow⟩ := below_result hBoundaryColumn hAtTop
  have hSelectedTargetRead : Canonical.cellAt mountain targetRef = .ok selectedTarget :=
    cellAt_ok_iff.mpr ⟨boundaryColumn, by simpa only [hTargetColumn] using hBoundaryColumn, hSelectedTarget⟩
  have hTargetEq : selectedTarget = target := Except.ok.inj (hSelectedTargetRead.symm.trans hTargetRead)
  subst selectedTarget
  obtain ⟨found, hFound⟩ := (below_succeeds_iff hBoundaryColumn query).mpr
    ⟨targetRef.index, target, hSelectedTarget, hTargetBelow.trans_le hQueryHigh⟩
  obtain ⟨hFoundColumn, foundCell, hFoundRead, hFoundBelow⟩ := below_result hBoundaryColumn hFound
  have hFoundLow : foundCell.row < p.lastTop.row := by
    by_contra hn
    have hHigh : p.lastTop.row ≤ foundCell.row := le_of_not_gt hn
    have hMem : foundCell.row ∈ boundaryColumn.toList.map Cell.row :=
      List.mem_map.mpr ⟨foundCell, List.mem_of_getElem?
        (by simpa only [Array.getElem?_toList] using hFoundRead), rfl⟩
    obtain ⟨oldCell, hOldMem, hOldRow⟩ := List.mem_map.mp ((hRows _ hHigh).mp hMem)
    obtain ⟨oldIndex, hOldIndex⟩ := List.mem_iff_getElem?.mp hOldMem
    obtain ⟨hc, hRootEq⟩ := Array.getElem?_eq_some_iff.mp hRootColumn
    have hCV : ColumnValid p.reduced p.root.column rootColumn := hRootEq ▸ p.reduced_valid _ hc
    have hStrict : StrictMono (fun i : Fin rootColumn.size => rootColumn[i.val].row) := by
      intro i j hij
      exact hCV.rows_strict _ _ _ _ (Array.getElem?_eq_getElem i.isLt)
        (Array.getElem?_eq_getElem j.isLt) hij
    have hAtMost := below_max_row hRootColumn hStrict hSourceBelow hSelectedSource
      (show rootColumn[oldIndex]? = some oldCell by simpa only [Array.getElem?_toList] using hOldIndex)
      (show oldCell.row < query by simpa only [hOldRow] using hFoundBelow)
    have hFoundLe : foundCell.row ≤ sourceCell.row := by simpa only [hOldRow] using hAtMost
    exact not_lt_of_ge hHigh (hFoundLe.trans_lt hSourceLow)
  have hIndexLe := below_max_index hBoundaryColumn hAtTop hFoundRead hFoundLow
  have hIndexGe := below_max_index hBoundaryColumn hFound hSelectedTarget (hTargetBelow.trans_le hQueryHigh)
  have hEqual : found = targetRef := by
    cases found
    cases targetRef
    simp only [Ref.mk.injEq]
    constructor <;> dsimp only at * <;> omega
  simpa only [hEqual] using hFound

/-- Actual boundary selection at the bad root's exact cap still gives
the selected target at a high child-upper query. The high-boundary fact
is derived from the successful outer loop, including a zero-copy prefix. -/
theorem DynamicBlockState.below_badRoot_high_query
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next copies : Nat}
    (s : DynamicBlockState p block start references next ambient) (hLast : 1 < last)
    (hStartRun : (forIn (List.range copies) p.reduced (fun block mountain => do
        let next ← copyBlock mountain p.marked p.boundaries p.root.column
          (p.initial.size - 1 - p.root.column) (block + 1)
        pure (.yield next)) : Result Mountain) = .ok start)
    {sourceIndex : Nat} {rootRow : Row}
    (a : ActualRootInterval p start ambient references sourceIndex rootRow)
    (hBadRoot : Frame.ref a.root = p.root) (hCap : Row.bump rootRow a.degree = p.lastTop.row)
    {child parent childUpper : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hParentRef : Frame.ref parent = p.root)
    (hUpper : (Frame.ofMountain p.reduced).upper child = some childUpper)
    (hChildHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height child) :
    below ambient (p.root.column + block * (p.reduced.size - 1 - p.root.column))
      ((Frame.ofMountain p.reduced).height childUpper) = .ok a.reference ∧
    Canonical.cellAt ambient a.reference = .ok a.target ∧
    a.reference.column = p.root.column + block * (p.reduced.size - 1 - p.root.column) ∧
    a.target.row ≤ (Frame.ofMountain p.reduced).height child ∧
    (Frame.ofMountain p.reduced).height childUpper =
      Row.B ((Frame.ofMountain p.reduced).height child) a.target.row := by
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hParentEq : parent = a.root := Executable.ref_injective F (hParentRef.trans hBadRoot.symm)
  have hParentRow : F.height parent = rootRow := by rw [hParentEq]; exact a.root_row
  have hParentColumn : parent.1.val = p.root.column := congrArg Ref.column hParentRef
  have hSourceBelow := canonical_below_of_parent p.reduced_valid hNormal hParent hUpper
  rw [hParentColumn] at hSourceBelow
  have hSourceLow : (F.cell parent).row < p.lastTop.row := by
    change F.height parent < p.lastTop.row
    rw [hParentRow, ← hCap]
    exact a.target_lower.trans_lt a.target_below
  have hSourceB : F.height childUpper = Row.B (F.height child) rootRow := by
    have hB := (Frame.aboveHeight_of_upper hUpper).symm.trans (hNormal.above_row hParent)
    change F.height childUpper = Row.B (F.height child) (F.height parent) at hB
    rw [hParentRow] at hB
    exact hB
  have hQueryHigh : p.lastTop.row ≤ F.height childUpper :=
    hChildHigh.trans ((Row.lt_B (F.height child) rootRow).le.trans_eq hSourceB.symm)
  have hAtTop : below start (start.size - 1) p.lastTop.row = .ok a.reference := by
    simpa only [hCap] using a.start_below
  have hBoundary := (p.blocks_high_root_boundary_of_success hLast hStartRun).2
  have hAtQuery := hBoundary.below_query_of_low_source hSourceBelow
    (cellAt_of_frame_node p.reduced parent) hSourceLow hAtTop a.target_start_read hQueryHigh
  have hColumnBound : start.size - 1 < start.size := by
    obtain ⟨nodes, hNodes, _⟩ := cellAt_ok_iff.mp a.target_start_read
    have hc := (Array.getElem?_eq_some_iff.mp hNodes).1
    simpa only [a.reference_column] using hc
  have hActual := (s.start_preserved.below hColumnBound _).trans hAtQuery
  have hBoundaryIndex : start.size - 1 =
      p.root.column + block * (p.reduced.size - 1 - p.root.column) := s.boundary_copy_index.symm
  rw [hBoundaryIndex] at hActual
  have hCapChild : Row.bump rootRow a.degree ≤ F.height child := by simpa only [hCap] using hChildHigh
  have hB : Row.B (F.height child) a.target.row = Row.B (F.height child) rootRow := by
    simpa only [Row.lift_at_root] using Row.B_fixed_child_lift_parent
      a.target_lower a.target_below (b := rootRow) le_rfl
      (a.target_lower.trans_lt a.target_below) hCapChild
  exact ⟨hActual, a.target_ambient_read, a.reference_column.trans hBoundaryIndex,
    a.target_below.le.trans hCapChild, hSourceB.trans hB.symm⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.HighRootBoundary.below_query_of_low_source
#print axioms OmegaY.Expansion.DynamicBlockState.below_badRoot_high_query
