/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PhysicalRootCommonBand.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualLowPhysicalCases

/-!
# Actual shared fill addends between physical and effective markers

The finite bands, their complete stored-parent alignment, and all endpoint
reads come from actual copying. The resulting common addend is cancelled,
including an empty band. Source values are never equated with copied values.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem bandValue_eq_of_row_read {mountain : Mountain} {column : Column} {columnIndex : Nat}
    (hValid : ColumnValid mountain columnIndex column) {start offset index : Nat} {cell : Cell}
    (hBound : start + offset < column.size) (hRead : column[index]? = some cell)
    (hRow : (column[start + offset]?.getD phantom).row = cell.row) :
    bandValue column start offset = cell.value := by
  have hAt : column[start + offset]? = some column[start + offset] := Array.getElem?_eq_getElem hBound
  have hRows : column[start + offset].row = cell.row := by simpa only [hAt, Option.getD_some] using hRow
  have hi := column_read_index_eq_of_row hValid hAt hRead hRows
  simp only [bandValue, hi, hRead, Option.getD_some]

namespace PhysicalMarkerRead

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start : Mountain} {references : List Ref}
  {u z parent : (Frame.ofMountain p.reduced).Node} {result : Mountain}
  {uCopy : EffectiveCopyOccurrence p block start references u result}
  {zCopy : EffectiveCopyOccurrence p block start references z result}
  (uPhysical : PhysicalMarkerRead uCopy) (zPhysical : PhysicalMarkerRead zCopy)

private theorem shared_addend_all_of_column_le (hLast : 1 < last)
    (hValid : MountainValid result) (hSums : MountainSums result)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUMarked : BucketMem p.marked u.1.val (Frame.ref u))
    (hZMarked : BucketMem p.marked z.1.val (Frame.ref z))
    (hRight : p.root.column ≤ parent.1.val) (hZColumn : z.1.val ≤ u.1.val) :
    ∃ addend, uPhysical.cell.value = uCopy.read.outputCell.value + addend ∧
      zPhysical.cell.value = zCopy.read.outputCell.value + addend := by
  let F := Frame.ofMountain p.reduced
  have hNormal : F.Normal := build_normal_of_success p.reduced_build
  obtain ⟨rootNodes, hRootNodes, hRootRead⟩ := Canonical.cellAt_ok_iff.mp p.restored_root
  obtain ⟨hRootBound, hRootEq⟩ := Array.getElem?_eq_some_iff.mp hRootNodes
  have hRootIndex : p.root.index < p.reduced[p.root.column].size := by
    rw [hRootEq]
    exact (Array.getElem?_eq_some_iff.mp hRootRead).1
  let root : F.Node := ⟨⟨p.root.column, hRootBound⟩, ⟨p.root.index, hRootIndex⟩⟩
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := p.markers_built
  have hURow : F.height u = F.height parent :=
    (build_marked_parent_bounds p.reduced_build hMarkers hUP hUMarked).2
  have hZRow : F.height z = F.height parent :=
    (build_marked_parent_bounds p.reduced_build hMarkers hZP hZMarked).2
  obtain ⟨zUpper, hZUpper⟩ := hNormal.upper_of_parent hZP
  have hHigher : F.height z < F.height zUpper := by
    have hSpec := Frame.upper_spec hZUpper
    rcases zUpper with ⟨column, index⟩
    dsimp only at hSpec
    obtain ⟨hColumn, hIndex⟩ := hSpec
    subst column
    exact hNormal.toOrdered.rows_strict z.1 (by change z.2.val < index.val; omega)
  have hSame : F.height z = F.height u := hZRow.trans hURow.symm
  let du := uCopy.data
  let dz := zCopy.data
  have hUSource : p.reduced[u.1.val]? = some du.sources :=
    (uCopy.state.base_ambient u.1.val u.1.isLt).symm.trans du.source_column
  have hZSource : p.reduced[z.1.val]? = some dz.sources :=
    (zCopy.state.base_ambient z.1.val z.1.isLt).symm.trans dz.source_column
  obtain ⟨_, hUPP, hUPL⟩ := uCopy.state.column_data_parent_inputs hLast u.1.isLt du
  obtain ⟨_, hZPP, hZPL⟩ := zCopy.state.column_data_parent_inputs hLast z.1.isLt dz
  have hUPreserve : PreservesColumns uCopy.before result :=
    (PreservesColumns.push uCopy.before uCopy.column).trans uCopy.preserved
  have hZPreserve : PreservesColumns zCopy.before result :=
    (PreservesColumns.push zCopy.before zCopy.column).trans zCopy.preserved
  have hSize : zCopy.before.size ≤ uCopy.before.size := by
    rw [zCopy.state.size_eq, uCopy.state.size_eq]
    exact Nat.add_le_add_right hZColumn _
  have hBetween := hZPreserve.between_prefixes hUPreserve hSize
  have hRefs : ∀ ref ∈ references, ValidRef zCopy.before ref := by
    intro ref hRef
    exact zCopy.state.start_preserved.validRef
      (RootRowsInColumn.references_valid zCopy.state.boundary_rows zCopy.state.reference_map ref hRef)
  obtain ⟨pair⟩ := build_common_parent_marker_bands p.reduced_build hMarkers hUP hZP hZUpper
    hSame.le (hSame ▸ hHigher) hRight du dz hUSource hZSource hUPP hUPL hZPP hZPL hBetween hRefs
    uCopy.read.copy_run zCopy.read.copy_run hUMarked
  let md := du.marker_data (Frame.ref u) hUMarked
  have hCurrent : md.current = F.cell u := Option.some.inj (md.current_at.symm.trans uCopy.read.source_at)
  have hUReference : referenceAt start references (F.height u) = .ok uCopy.read.outputCell.row :=
    (uCopy.state.referenceAt_preserved _).symm.trans (uCopy.read.marked_reference hUMarked)
  have hZReference : referenceAt start references (F.height z) = .ok zCopy.read.outputCell.row :=
    (zCopy.state.referenceAt_preserved _).symm.trans (zCopy.read.marked_reference hZMarked)
  have hTargetReference : referenceAt start references (F.height u) = .ok md.targetCell.row := by
    have h := (uCopy.state.referenceAt_preserved md.current.row).symm.trans md.reference
    simpa only [hCurrent, Frame.height] using h
  have hTargetU : md.targetCell.row = uCopy.read.outputCell.row :=
    Except.ok.inj (hTargetReference.symm.trans hUReference)
  have hTargetZ : md.targetCell.row = zCopy.read.outputCell.row := by
    rw [hSame] at hZReference
    exact Except.ok.inj (hTargetReference.symm.trans hZReference)
  have hFinalU : result[uCopy.before.size]? = some uCopy.column := uCopy.preserved.column_read (by simp)
  have hFinalZ : result[zCopy.before.size]? = some zCopy.column := zCopy.preserved.column_read (by simp)
  obtain ⟨hu, hUColumn⟩ := Array.getElem?_eq_some_iff.mp hFinalU
  obtain ⟨hz, hZColumnEq⟩ := Array.getElem?_eq_some_iff.mp hFinalZ
  have hUValid : ColumnValid result uCopy.before.size uCopy.column := hUColumn ▸ hValid _ hu
  have hZValid : ColumnValid result zCopy.before.size zCopy.column := hZColumnEq ▸ hValid _ hz
  have hUBottom : bandValue uCopy.column pair.leftBand.start 0 = uPhysical.cell.value :=
    bandValue_eq_of_row_read hUValid (by have := pair.leftBand.bound; omega) uPhysical.output_at
      (by simpa only [Nat.add_zero] using pair.leftBand.low_row.trans (hURow.symm.trans uPhysical.source_row.symm))
  have hZBottom : bandValue zCopy.column pair.rightBand.start 0 = zPhysical.cell.value :=
    bandValue_eq_of_row_read hZValid (by have := pair.rightBand.bound; omega) zPhysical.output_at
      (by simpa only [Nat.add_zero] using pair.rightBand.low_row.trans (hZRow.symm.trans zPhysical.source_row.symm))
  have hUTop : bandValue uCopy.column pair.leftBand.start pair.gap.length = uCopy.read.outputCell.value :=
    bandValue_eq_of_row_read hUValid pair.leftBand.bound uCopy.read.output_at
      (pair.leftBand.high_row.trans hTargetU)
  have hZTop : bandValue zCopy.column pair.rightBand.start pair.gap.length = zCopy.read.outputCell.value :=
    bandValue_eq_of_row_read hZValid pair.rightBand.bound zCopy.read.output_at
      (pair.rightBand.high_row.trans hTargetZ)
  obtain ⟨addend, hU, hZ⟩ := hSums.common_band_addend hValid hFinalU hFinalZ
    pair.leftBand.start_positive pair.rightBand.start_positive pair.leftBand.bound pair.rightBand.bound
    (pair.leftBand.parentsAgree pair.rightBand)
  exact ⟨addend, by simpa only [hUBottom, hUTop] using hU,
    by simpa only [hZBottom, hZTop] using hZ⟩

/-- The actual shared fill contribution is one common natural number.
The theorem includes zero-height gaps; no nonempty-fill premise is used. -/
theorem shared_addend_all (hLast : 1 < last)
    (hValid : MountainValid result) (hSums : MountainSums result)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUMarked : BucketMem p.marked u.1.val (Frame.ref u))
    (hZMarked : BucketMem p.marked z.1.val (Frame.ref z))
    (hRight : p.root.column ≤ parent.1.val) :
    ∃ addend, uPhysical.cell.value = uCopy.read.outputCell.value + addend ∧
      zPhysical.cell.value = zCopy.read.outputCell.value + addend := by
  rcases le_total z.1.val u.1.val with hZU | hUZ
  · exact uPhysical.shared_addend_all_of_column_le zPhysical hLast hValid hSums hUP hZP hUMarked hZMarked hRight hZU
  · obtain ⟨addend, hZ, hU⟩ := zPhysical.shared_addend_all_of_column_le uPhysical hLast hValid hSums
      hZP hUP hZMarked hUMarked hRight hUZ
    exact ⟨addend, hU, hZ⟩

theorem compare_effective_all (hLast : 1 < last)
    (hValid : MountainValid result) (hSums : MountainSums result)
    (hUP : (Frame.ofMountain p.reduced).P u = some parent)
    (hZP : (Frame.ofMountain p.reduced).P z = some parent)
    (hUMarked : BucketMem p.marked u.1.val (Frame.ref u))
    (hZMarked : BucketMem p.marked z.1.val (Frame.ref z))
    (hRight : p.root.column ≤ parent.1.val) :
    (uPhysical.cell.value ≤ zPhysical.cell.value ↔ uCopy.read.outputCell.value ≤ zCopy.read.outputCell.value) ∧
    (uPhysical.cell.value < zPhysical.cell.value ↔ uCopy.read.outputCell.value < zCopy.read.outputCell.value) := by
  obtain ⟨addend, hU, hZ⟩ := uPhysical.shared_addend_all zPhysical hLast hValid hSums hUP hZP hUMarked hZMarked hRight
  omega

end PhysicalMarkerRead
end OmegaY.Expansion

#print axioms OmegaY.Expansion.PhysicalMarkerRead.shared_addend_all
#print axioms OmegaY.Expansion.PhysicalMarkerRead.compare_effective_all

