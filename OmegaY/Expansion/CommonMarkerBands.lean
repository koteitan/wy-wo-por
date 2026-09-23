/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonMarkerBands.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CommonMarkerBlocker
import OmegaY.Expansion.CommonBackfillBand
import OmegaY.Expansion.FillAdjacent
import OmegaY.Expansion.ActualIntervalEdge

/-!
# Continuous physical-marker to effective-target bands

The band positions and their upper-stored reference alignment are derived
from actual segment sorting and finishing. The empty fill is included: its
physical and effective endpoint is the same node. The physical marker's
incoming leg is not part of the alignment.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- A concrete finished interval, with all cells strictly above its bottom
matching the actual ascending fill list. The read bounds prevent defaults
from supplying any of the stated endpoints or parents. -/
structure MarkerBand (column : Column) (gap : List Cell) (low high : Row) where
  start : Nat
  start_positive : 0 < start
  bound : start + gap.length < column.size
  low_row : (column[start]?.getD phantom).row = low
  high_row : (column[start + gap.length]?.getD phantom).row = high
  upper_shape : ∀ i (hi : i < gap.length),
    SameShape gap[i] (column[start + i + 1]?.getD phantom)

private theorem splice_read {before fragment after : List Cell} {index : Nat} {cell : Cell}
    (hRead : fragment[index]? = some cell) :
    (before ++ fragment ++ after)[before.length + index]? = some cell := by
  have hi := (List.getElem?_eq_some_iff.mp hRead).1
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]
  exact hRead

namespace ColumnCopyData

variable {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
  {sourceColumn shift rootColumn : Nat}
  (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)

/-- The physical marker and its entire fill occupy one consecutive block
of the real candidate sort. In particular, no contour cell can interrupt it. -/
theorem marker_fill_splice
    (hPP : ∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hPL : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[i]? = some cell ∧ cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {marker : Ref} (hm : marker ∈ d.bucket) :
    ∃ before after copied,
      copied.row = (d.marker_data marker hm).current.row ∧
      finishSort d.candidates = before ++
        (copied :: fillCellsAscending (d.marker_data marker hm).parentNodes
          ((d.marker_data marker hm).sourceParent.column + shift)
          (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row) ++ after := by
  let md := d.marker_data marker hm
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hPL marker hm
  obtain ⟨copied, path, hCopied, _, hSegment⟩ := copySegment_sorted_splice d.ambient_valid
    d.source_column d.source_nonzero d.destination.le d.source_top (d.bucket.map Ref.index) md
    (hPP marker hm) hLow hLowRow (d.segment_run hm)
  obtain ⟨before, after, hSplit⟩ := List.append_of_mem (List.mem_reverse.mpr hm)
  let sortedSegment := fun entry => finishSort (d.segment entry)
  refine ⟨before.flatMap sortedSegment, path ++ after.flatMap sortedSegment, copied,
    copyEdge_return_row hCopied, ?_⟩
  rw [d.finishSort_candidates_cells hPP hPL hNoPremature]
  simp only [ascendingCells, hSplit, List.flatMap_append, List.flatMap_cons]
  rw [hSegment]
  simp only [List.append_assoc, List.cons_append, List.nil_append, sortedSegment, md]

/-- Actual copy-and-finish execution supplies the whole interval, including
its two endpoint rows and every upper-stored reference at its exact offset. -/
theorem copyColumn_marker_band
    (hPP : ∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hPL : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[i]? = some cell ∧ cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hPositive : 0 < (d.marker_data marker hm).current.row) :
    Nonempty (MarkerBand column
      (fillCellsAscending (d.marker_data marker hm).parentNodes
        ((d.marker_data marker hm).sourceParent.column + shift)
        (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row)
      (d.marker_data marker hm).current.row (d.marker_data marker hm).targetCell.row) := by
  let md := d.marker_data marker hm
  let gap := fillCellsAscending md.parentNodes (md.sourceParent.column + shift) md.current.row md.targetCell.row
  obtain ⟨before, after, copied, hCopiedRow, hSplit⟩ := d.marker_fill_splice hPP hPL hNoPremature hm
  have hFinish := d.copyColumn_eq_finish.symm.trans hRun
  have hShape := (finish_success_spec hFinish).1
  change ColumnShape (finishSort d.candidates) column at hShape
  rw [hSplit] at hShape
  have hLength : before.length + (gap.length + 1) + after.length = column.size := by
    simpa only [List.length_append, List.length_cons, gap, md] using hShape.length
  have hBound : before.length + gap.length < column.size := by omega
  obtain ⟨bottom, hBottom, hBottomShape⟩ := hShape.source_getElem
    (splice_read (before := before) (after := after)
      (show (copied :: gap)[0]? = some copied from rfl))
  simp only [Nat.add_zero] at hBottom
  have hBottomRow : (column[before.length]?.getD phantom).row = md.current.row := by
    rw [hBottom]
    exact hBottomShape.1.symm.trans hCopiedRow
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have hActualEq : actual = column := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  have hStart : 0 < before.length := by
    by_contra hn
    have hz : before.length = 0 := by omega
    rw [hz, hValid.phantom] at hBottomRow
    exact (not_lt_of_ge hBottomRow.ge) hPositive
  obtain ⟨lowIndex, lowCell, hLow, hLowRow⟩ := hPL marker hm
  obtain ⟨hp, hParentEq⟩ := Array.getElem?_eq_some_iff.mp md.parent_nodes
  have hParentValid : ColumnValid mountain (md.sourceParent.column + shift) md.parentNodes :=
    hParentEq ▸ d.ambient_valid _ hp
  have hEnd := (fillCellsAscendingRows_power_steps hParentValid.rows_strict (hPP marker hm)
    hLow md.target_at (by simpa only [hLowRow] using md.target_lower)
    (column := md.sourceParent.column + shift)).2
  rw [hLowRow] at hEnd
  have hFragmentEnd : ((copied :: gap).map Cell.row).getLast? = some md.targetCell.row := by
    simpa only [List.map_cons, gap, fillCellsAscending_rows, hCopiedRow, md] using hEnd
  have hLastRead : (copied :: gap)[gap.length]? = some (copied :: gap)[gap.length] :=
    List.getElem?_eq_getElem (by simp)
  have hLastRow : (copied :: gap)[gap.length].row = md.targetCell.row := by
    rw [List.getLast?_eq_getElem?] at hFragmentEnd
    simpa only [List.length_map, List.length_cons, Nat.add_sub_cancel_right,
      List.getElem?_map, hLastRead, Option.map_some, Option.some.injEq] using hFragmentEnd
  obtain ⟨topCell, hTop, hTopShape⟩ := hShape.source_getElem
    (splice_read (before := before) (after := after) hLastRead)
  refine ⟨{
    start := before.length
    start_positive := hStart
    bound := hBound
    low_row := hBottomRow
    high_row := ?_
    upper_shape := ?_ }⟩
  · rw [hTop]
    exact hTopShape.1.symm.trans hLastRow
  · intro i hi
    have hRead : (copied :: gap)[i + 1]? = some gap[i] := by
      simp only [List.getElem?_cons_succ]
      exact List.getElem?_eq_getElem hi
    obtain ⟨cell, hCell, hSame⟩ := hShape.source_getElem
      (splice_read (before := before) (after := after) hRead)
    rw [show before.length + i + 1 = before.length + (i + 1) by omega, hCell]
    exact hSame

end ColumnCopyData

/-- The exact shared ascending fill identifies all upper-stored references;
the bottom markers' incoming references are not compared. -/
theorem MarkerBand.parentsAgree {left right : Column} {gap : List Cell} {lowLeft lowRight highLeft highRight : Row}
    (hLeft : MarkerBand left gap lowLeft highLeft) (hRight : MarkerBand right gap lowRight highRight) :
    BandParentsAgree left right hLeft.start hRight.start gap.length := by
  intro i hi
  exact (hLeft.upper_shape i hi).2.symm.trans (hRight.upper_shape i hi).2

/-- Two finished intervals obtained from the same real fill. This is an
output certificate: the construction theorem below provides it from the
source marker test and both real copy executions. -/
structure CommonMarkerBandPair (left right : Column) (low high : Row) where
  gap : List Cell
  leftBand : MarkerBand left gap low high
  rightBand : MarkerBand right gap low high

theorem CommonMarkerBandPair.compare {mountain : Mountain}
    (hSums : MountainSums mountain) (hValid : MountainValid mountain)
    {leftColumn rightColumn : Nat} {left right : Column} {low high : Row}
    (pair : CommonMarkerBandPair left right low high)
    (hLeft : mountain[leftColumn]? = some left) (hRight : mountain[rightColumn]? = some right) :
    (bandValue left pair.leftBand.start 0 ≤ bandValue right pair.rightBand.start 0 ↔
      bandValue left pair.leftBand.start pair.gap.length ≤ bandValue right pair.rightBand.start pair.gap.length) ∧
    (bandValue left pair.leftBand.start 0 < bandValue right pair.rightBand.start 0 ↔
      bandValue left pair.leftBand.start pair.gap.length < bandValue right pair.rightBand.start pair.gap.length) :=
  hSums.common_band_compare hValid hLeft hRight pair.leftBand.start_positive pair.rightBand.start_positive
    pair.leftBand.bound pair.rightBand.bound (pair.leftBand.parentsAgree pair.rightBand)

/-- The source common-parent blocker hypotheses supply both actual marked
bands. Only the first membership is given; the second and the shared fill
are theorems. Earlier and later copied columns use the same frozen block
references and unchanged completed parent columns. -/
theorem build_common_parent_marker_bands {input : List Nat} {source before after : Mountain}
    (hBuild : build input = .ok source)
    {root u z parent zUpper : (Frame.ofMountain source).Node}
    {marked : Array (List Ref)} {references : List Ref} {shift : Nat}
    (hMarkers : markers source (Frame.ref root) = .ok marked)
    (hUParent : (Frame.ofMountain source).P u = some parent)
    (hZParent : (Frame.ofMountain source).P z = some parent)
    (hZUpper : (Frame.ofMountain source).upper z = some zUpper)
    (hOrder : (Frame.ofMountain source).height z ≤ (Frame.ofMountain source).height u)
    (hBefore : (Frame.ofMountain source).height u < (Frame.ofMountain source).height zUpper)
    (hParentRight : root.1.val ≤ parent.1.val)
    (du : ColumnCopyData after marked references u.1.val shift root.1.val)
    (dz : ColumnCopyData before marked references z.1.val shift root.1.val)
    (hUSource : source[u.1.val]? = some du.sources)
    (hZSource : source[z.1.val]? = some dz.sources)
    (hUPP : ∀ marker (hm : marker ∈ du.bucket), ColumnPowerSteps (du.marker_data marker hm).parentNodes)
    (hUPL : ∀ marker (hm : marker ∈ du.bucket), ∃ (i : Nat) (cell : Cell),
      (du.marker_data marker hm).parentNodes[i]? = some cell ∧ cell.row = (du.marker_data marker hm).current.row)
    (hZPP : ∀ marker (hm : marker ∈ dz.bucket), ColumnPowerSteps (dz.marker_data marker hm).parentNodes)
    (hZPL : ∀ marker (hm : marker ∈ dz.bucket), ∃ (i : Nat) (cell : Cell),
      (dz.marker_data marker hm).parentNodes[i]? = some cell ∧ cell.row = (dz.marker_data marker hm).current.row)
    (hPreserve : PreservesColumns before after)
    (hRefs : ∀ ref ∈ references, ValidRef before ref)
    {uColumn zColumn : Column}
    (hURun : copyColumn after marked references u.1.val shift root.1.val = .ok uColumn)
    (hZRun : copyColumn before marked references z.1.val shift root.1.val = .ok zColumn)
    (hUMarker : BucketMem marked (Frame.ref u).column (Frame.ref u)) :
    Nonempty (CommonMarkerBandPair uColumn zColumn ((Frame.ofMountain source).height parent)
      (du.marker_data (Frame.ref u) hUMarker).targetCell.row) := by
  let F := Frame.ofMountain source
  have hNormal : F.Normal := build_normal_of_success hBuild
  have hZMarker := (build_common_parent_marker_iff hBuild hMarkers hUParent hZParent hZUpper
    hOrder hBefore hParentRight).mp hUMarker
  let mu := du.marker_data (Frame.ref u) hUMarker
  let mz := dz.marker_data (Frame.ref z) hZMarker
  obtain ⟨hURef, hZRef, hRows, hColumn, _, hTarget⟩ := build_common_parent_marker_data hBuild
    hMarkers hUParent hZParent hZUpper hOrder hBefore hParentRight (.inl hUMarker)
    mu mz hUSource hZSource dz.ambient_valid hPreserve hRefs
  obtain ⟨_, _, hURow, hZRow, _⟩ := build_common_parent_marker_rows hBuild hMarkers
    hUParent hZParent hZUpper hOrder hBefore hParentRight (.inl hUMarker)
  have hUCell : mu.current = F.cell u := Except.ok.inj
    ((Canonical.cellAt_ok_iff.mpr (show ∃ nodes, source[(Frame.ref u).column]? = some nodes ∧
      nodes[(Frame.ref u).index]? = some mu.current from ⟨du.sources, hUSource, mu.current_at⟩)).symm.trans
      (Canonical.cellAt_of_frame_node source u))
  have hZCell : mz.current = F.cell z := Except.ok.inj
    ((Canonical.cellAt_ok_iff.mpr (show ∃ nodes, source[(Frame.ref z).column]? = some nodes ∧
      nodes[(Frame.ref z).index]? = some mz.current from ⟨dz.sources, hZSource, mz.current_at⟩)).symm.trans
      (Canonical.cellAt_of_frame_node source z))
  have hParentReal := Frame.real_of_value_pos hNormal.toOrdered (Frame.P_value hNormal.toOrdered hUParent).1
  have hParentPositive := Row.zero_lt_one.trans_le (Frame.one_le_height hNormal.toOrdered hParentReal)
  have hUCurrent : mu.current.row = F.height parent := by rw [hUCell]; exact hURow
  have hZCurrent : mz.current.row = F.height parent := by rw [hZCell]; exact hZRow
  obtain ⟨uBand⟩ := du.copyColumn_marker_band hUPP hUPL
    (build_source_no_premature_one hBuild hUSource) hURun hUMarker
    (show 0 < mu.current.row by rw [hUCurrent]; exact hParentPositive)
  obtain ⟨zBand⟩ := dz.copyColumn_marker_band hZPP hZPL
    (build_source_no_premature_one hBuild hZSource) hZRun hZMarker
    (show 0 < mz.current.row by rw [hZCurrent]; exact hParentPositive)
  have hParentRef : mu.sourceParent = mz.sourceParent := hURef.trans hZRef.symm
  have hGap : fillCellsAscending mu.parentNodes (mu.sourceParent.column + shift)
      mu.current.row mu.targetCell.row =
      fillCellsAscending mz.parentNodes (mz.sourceParent.column + shift) mz.current.row mz.targetCell.row := by
    rw [hColumn, hParentRef, hRows, hTarget]
  change MarkerBand uColumn
    (fillCellsAscending mu.parentNodes (mu.sourceParent.column + shift) mu.current.row mu.targetCell.row)
    mu.current.row mu.targetCell.row at uBand
  change MarkerBand zColumn
    (fillCellsAscending mz.parentNodes (mz.sourceParent.column + shift) mz.current.row mz.targetCell.row)
    mz.current.row mz.targetCell.row at zBand
  rw [← hGap, hZCurrent, ← hTarget] at zBand
  rw [hUCurrent] at uBand
  -- Rewriting the endpoint also rewrites its occurrences inside the gap.
  rw [hUCurrent] at zBand
  exact ⟨⟨_, uBand, zBand⟩⟩

/-- Complete numerical comparison for the two actual copied marker bands.
The final mountain's sums and validity are the only global invariants; the
band positions and matching stored parents are all derived above. -/
theorem build_common_parent_marker_band_compare {input : List Nat} {source before after final : Mountain}
    (hBuild : build input = .ok source)
    {root u z parent zUpper : (Frame.ofMountain source).Node}
    {marked : Array (List Ref)} {references : List Ref} {shift : Nat}
    (hMarkers : markers source (Frame.ref root) = .ok marked)
    (hUParent : (Frame.ofMountain source).P u = some parent)
    (hZParent : (Frame.ofMountain source).P z = some parent)
    (hZUpper : (Frame.ofMountain source).upper z = some zUpper)
    (hOrder : (Frame.ofMountain source).height z ≤ (Frame.ofMountain source).height u)
    (hBefore : (Frame.ofMountain source).height u < (Frame.ofMountain source).height zUpper)
    (hParentRight : root.1.val ≤ parent.1.val)
    (du : ColumnCopyData after marked references u.1.val shift root.1.val)
    (dz : ColumnCopyData before marked references z.1.val shift root.1.val)
    (hUSource : source[u.1.val]? = some du.sources)
    (hZSource : source[z.1.val]? = some dz.sources)
    (hUPP : ∀ marker (hm : marker ∈ du.bucket), ColumnPowerSteps (du.marker_data marker hm).parentNodes)
    (hUPL : ∀ marker (hm : marker ∈ du.bucket), ∃ (i : Nat) (cell : Cell),
      (du.marker_data marker hm).parentNodes[i]? = some cell ∧ cell.row = (du.marker_data marker hm).current.row)
    (hZPP : ∀ marker (hm : marker ∈ dz.bucket), ColumnPowerSteps (dz.marker_data marker hm).parentNodes)
    (hZPL : ∀ marker (hm : marker ∈ dz.bucket), ∃ (i : Nat) (cell : Cell),
      (dz.marker_data marker hm).parentNodes[i]? = some cell ∧ cell.row = (dz.marker_data marker hm).current.row)
    (hPreserve : PreservesColumns before after)
    (hRefs : ∀ ref ∈ references, ValidRef before ref)
    {uColumn zColumn : Column}
    (hURun : copyColumn after marked references u.1.val shift root.1.val = .ok uColumn)
    (hZRun : copyColumn before marked references z.1.val shift root.1.val = .ok zColumn)
    (hUMarker : BucketMem marked (Frame.ref u).column (Frame.ref u))
    (hFinalValid : MountainValid final) (hFinalSums : MountainSums final)
    (hFinalU : final[after.size]? = some uColumn) (hFinalZ : final[before.size]? = some zColumn) :
    ∃ pair : CommonMarkerBandPair uColumn zColumn ((Frame.ofMountain source).height parent)
        (du.marker_data (Frame.ref u) hUMarker).targetCell.row,
      (bandValue uColumn pair.leftBand.start 0 ≤ bandValue zColumn pair.rightBand.start 0 ↔
        bandValue uColumn pair.leftBand.start pair.gap.length ≤
          bandValue zColumn pair.rightBand.start pair.gap.length) ∧
      (bandValue uColumn pair.leftBand.start 0 < bandValue zColumn pair.rightBand.start 0 ↔
        bandValue uColumn pair.leftBand.start pair.gap.length <
          bandValue zColumn pair.rightBand.start pair.gap.length) := by
  obtain ⟨pair⟩ := build_common_parent_marker_bands hBuild hMarkers hUParent hZParent hZUpper
    hOrder hBefore hParentRight du dz hUSource hZSource hUPP hUPL hZPP hZPL hPreserve hRefs
    hURun hZRun hUMarker
  exact ⟨pair, pair.compare hFinalSums hFinalValid hFinalU hFinalZ⟩

/-- For an actual expansion, the global numeric invariants in the previous
theorem need not be assumed. This small composition applies also to bands
whose positions were derived by `build_common_parent_marker_bands`. -/
theorem CommonMarkerBandPair.expand_compare {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {final : Mountain} (hRun : expandDiagram values copies = .ok final)
    {leftColumn rightColumn : Nat} {left right : Column} {low high : Row}
    (pair : CommonMarkerBandPair left right low high)
    (hLeft : final[leftColumn]? = some left) (hRight : final[rightColumn]? = some right) :
    (bandValue left pair.leftBand.start 0 ≤ bandValue right pair.rightBand.start 0 ↔
      bandValue left pair.leftBand.start pair.gap.length ≤ bandValue right pair.rightBand.start pair.gap.length) ∧
    (bandValue left pair.leftBand.start 0 < bandValue right pair.rightBand.start 0 ↔
      bandValue left pair.leftBand.start pair.gap.length < bandValue right pair.rightBand.start pair.gap.length) :=
  pair.compare (expandDiagram_equations hLegal hRun).1 (expandDiagram_valid_of_success hLegal hRun) hLeft hRight

end OmegaY.Expansion

#print axioms OmegaY.Expansion.ColumnCopyData.marker_fill_splice
#print axioms OmegaY.Expansion.ColumnCopyData.copyColumn_marker_band
#print axioms OmegaY.Expansion.MarkerBand.parentsAgree
#print axioms OmegaY.Expansion.CommonMarkerBandPair.compare
#print axioms OmegaY.Expansion.build_common_parent_marker_bands
#print axioms OmegaY.Expansion.build_common_parent_marker_band_compare
#print axioms OmegaY.Expansion.CommonMarkerBandPair.expand_compare
