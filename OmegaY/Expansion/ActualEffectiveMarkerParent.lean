/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualEffectiveMarkerParent.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualEffectiveParent
import OmegaY.Expansion.MarkerContourGeometry
import OmegaY.Expansion.CommonMarkerBlocker

/-!
# Effective stored parents of actual weak markers

The effective occurrence is the selected reference target. Its outgoing
stored edge is supplied by the actual first contour cell, or, for an
unraised target, by the actual next physical marker. No numerical parent
search on a copied column is presumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem EffectiveCopyRead.marker_index_of_marked
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn sourceIndex : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {sourceCell : Cell} {column : Column}
    (read : EffectiveCopyRead d sourceIndex sourceCell column)
    (hMarked : (⟨sourceColumn, sourceIndex⟩ : Ref) ∈ d.bucket) :
    read.marker.index = sourceIndex := by
  have hBefore := read.marker_before
  by_contra hn
  exact read.no_between sourceIndex (by omega) le_rfl
    (List.mem_map.mpr ⟨⟨sourceColumn, sourceIndex⟩, hMarked, rfl⟩)

theorem EffectiveCopyRead.marked_reference
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn sourceIndex : Nat}
    {d : ColumnCopyData mountain marked references sourceColumn shift rootColumn}
    {sourceCell : Cell} {column : Column}
    (read : EffectiveCopyRead d sourceIndex sourceCell column)
    (hMarked : (⟨sourceColumn, sourceIndex⟩ : Ref) ∈ d.bucket) :
    referenceAt mountain references sourceCell.row = .ok read.outputCell.row := by
  have hIndex := read.marker_index_of_marked hMarked
  have hCurrent : (d.marker_data read.marker read.marker_mem).current = sourceCell :=
    Option.some.inj ((d.marker_data read.marker read.marker_mem).current_at.symm.trans
      (by simpa only [hIndex] using read.source_at))
  have hRow := read.output_row
  rw [hCurrent, Row.lift_at_root] at hRow
  simpa only [hCurrent, hRow] using (d.marker_data read.marker read.marker_mem).reference

private theorem successor_read_adjacent {mountain : Mountain} {c : Nat} {column : Column}
    (hValid : ColumnValid mountain c column) {i j : Nat} {lower upper : Cell}
    (hLower : column[i]? = some lower) (hUpper : column[j]? = some upper)
    (hRows : upper.row = Row.bump lower.row 0) : j = i + 1 := by
  have hStrict : lower.row < upper.row := hRows ▸ Row.lt_bump lower.row 0
  have hOrder : i < j := by
    by_contra hn
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_gt hn) with hj | rfl
    · exact (not_lt_of_ge (hValid.rows_strict _ _ _ _ hUpper hLower hj).le) hStrict
    · exact (ne_of_lt hStrict) (congrArg Cell.row (Option.some.inj (hLower.symm.trans hUpper)))
  by_contra hn
  have hBound : i + 1 < column.size := lt_trans (by omega) (Array.getElem?_eq_some_iff.mp hUpper).1
  have hMiddle : column[i + 1]? = some column[i + 1] := Array.getElem?_eq_getElem hBound
  have hLo := hValid.rows_strict _ _ _ _ hLower hMiddle (Nat.lt_succ_self i)
  have hHi := hValid.rows_strict _ _ _ _ hMiddle hUpper (by omega)
  rw [hRows] at hHi
  have he := Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero (Row.jump_le_of_lt_bump hLo.le hHi))
  exact (ne_of_lt hLo) he

/-- The effective endpoint of a real successor marker has the actual
target reference as its stored parent. Both raised and unraised targets
are covered, including an immediately following physical marker. -/
theorem ColumnCopyData.effective_marker_upper
    {mountain : Mountain} {marked : Array (List Ref)} {references : List Ref}
    {sourceColumn shift rootColumn : Nat}
    (d : ColumnCopyData mountain marked references sourceColumn shift rootColumn)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket),
      ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (index : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[index]? = some cell ∧
        cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain marked references sourceColumn shift rootColumn = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hUpper : (d.marker_data marker hm).upper.row = Row.bump (d.marker_data marker hm).current.row 0)
    (hRoot : rootColumn ≤ (d.marker_data marker hm).sourceParent.column)
    {index : Nat} {lower : Cell} (hLower : column[index]? = some lower)
    (hLowerRow : lower.row = (d.marker_data marker hm).targetCell.row) :
    ∃ upper, column[index + 1]? = some upper ∧
      upper.row = Row.bump (d.marker_data marker hm).targetCell.row 0 ∧
      upper.left = some ⟨(d.marker_data marker hm).sourceParent.column + shift,
        (d.marker_data marker hm).targetIndex⟩ := by
  let md := d.marker_data marker hm
  change rootColumn ≤ md.sourceParent.column at hRoot
  obtain ⟨actual, hActual, _, hValid, _, _⟩ := d.copyColumn_valid
  have he : actual = column := Except.ok.inj (hActual.symm.trans hRun)
  subst actual
  by_cases hRaised : md.current.row < md.targetCell.row
  · obtain ⟨step, hLo, hHi⟩ := d.copyColumn_fill_contour_seam hParentPower hParentLow
      hNoPremature hRun hm hUpper hRoot hRaised
    have hIndex : step.position = index := column_read_index_eq_of_row hValid
      step.lower_at hLower (hLo.trans hLowerRow.symm)
    exact ⟨step.upper, hIndex ▸ step.upper_at, hHi, step.upper_left⟩
  · have hEqual : md.targetCell.row = md.current.row := le_antisymm
      (le_of_not_gt hRaised) md.target_lower
    let expected : Cell := ⟨Row.bump md.targetCell.row 0, 0,
      some ⟨md.sourceParent.column + shift, md.targetIndex⟩⟩
    have hUpperRead : lookup mountain ⟨sourceColumn, marker.index + 1⟩ = .ok md.upper :=
      lookup_ok_iff.mpr ⟨d.sources, d.source_column, md.upper_at⟩
    have hNonzero : md.upper.row ≠ 0 := by
      rw [show md.upper.row = Row.bump md.current.row 0 from hUpper]
      exact ne_of_gt ((Row.zero_le _).trans_lt (Row.lt_bump _ _))
    have hTargetRead : Canonical.cellAt mountain ⟨md.sourceParent.column + shift, md.targetIndex⟩ =
        .ok md.targetCell := cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, md.target_at⟩
    have hBelow := below_bump_zero_of_read d.ambient_valid hTargetRead
    have hDest : md.sourceParent.column + shift < sourceColumn + shift := by
      rw [d.destination]
      exact (Array.getElem?_eq_some_iff.mp md.parent_nodes).1
    have hCopy : copyEdge mountain ⟨sourceColumn, marker.index + 1⟩ shift rootColumn
        md.upper.row = .ok expected := by
      have hUpperTarget : md.upper.row = Row.bump md.targetCell.row 0 := by
        simpa only [hEqual] using hUpper
      have hTargetNonzero : Row.bump md.targetCell.row 0 ≠ 0 := hUpperTarget ▸ hNonzero
      simp [copyEdge, hUpperRead, hUpperTarget, hTargetNonzero, leftOf, md.upper_left,
        not_lt_of_ge hRoot, hBelow, Nat.not_le_of_gt hDest, expected]
    have hCandidate : expected ∈ d.candidates := by
      by_cases hMarked : marker.index + 1 ∈ d.bucket.map Ref.index
      · obtain ⟨higher, hHigher, hIndex⟩ := List.mem_map.mp hMarked
        let hd := d.marker_data higher hHigher
        have hCurrent : hd.current = md.upper := Option.some.inj
          (hd.current_at.symm.trans (by simpa only [hIndex] using md.upper_at))
        obtain ⟨copied, path, gap, hResult, hCopied, _, _, _, _, _, _, _⟩ :=
          copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero
            d.destination.le d.source_top references (d.bucket.map Ref.index) hd.current_at
            hd.upper_at hd.upper_left hd.parent_nodes hd.target_at hd.reference hd.target_lower
            (d.segment_run hHigher)
        have hSame : copied = expected := Except.ok.inj
          (hCopied.symm.trans (by simpa only [hIndex, hCurrent] using hCopy))
        exact List.mem_flatMap.mpr ⟨higher, hHigher, by simp [hResult, hSame]⟩
      · obtain ⟨copied, path, gap, hResult, _, _, _, hContour, _, _, _, _⟩ :=
          copySegment_result_decomposition d.ambient_valid d.source_column d.source_nonzero
            d.destination.le d.source_top references (d.bucket.map Ref.index) md.current_at
            md.upper_at md.upper_left md.parent_nodes md.target_at md.reference md.target_lower
            (d.segment_run hm)
        have hSourceMem := mem_contourSourceCells_of_no_between hNoPremature
          (d.bucket.map Ref.index) md.current_at md.upper_at (Nat.lt_succ_self _)
          (by
            intro middle hLo hHi
            have he : middle = marker.index + 1 := by omega
            simpa only [he] using hMarked) rfl
        have hRows := contour_rows_eq_lift_of_success d.ambient_valid d.source_column d.source_nonzero
          d.destination.le d.source_top d.source_power (d.bucket.map Ref.index)
          md.targetCell.row md.current_at rfl hContour
        have hNonempty : path ≠ [] := by
          intro he
          have hMem : Row.lift md.current.row md.targetCell.row md.upper.row ∈ path.map Cell.row := by
            rw [hRows]
            exact List.mem_map.mpr ⟨md.upper, hSourceMem, rfl⟩
          simp only [he, List.map_nil, List.not_mem_nil] at hMem
        obtain ⟨head, tail, hPath⟩ := List.exists_cons_of_ne_nil hNonempty
        have hHead : path.head? = some head := by simp only [hPath, List.head?_cons]
        have hHeadEq := d.successor_contour_head_of_read hm hUpper hRoot hContour hHead
        exact List.mem_flatMap.mpr ⟨marker, hm, by simp [hResult, hPath, hHeadEq, expected, md]⟩
    obtain ⟨j, upper, hRead, hShape⟩ := finish_candidate_read
      (d.copyColumn_eq_finish.symm.trans hRun) hCandidate
    have hRow : upper.row = Row.bump md.targetCell.row 0 := hShape.1.symm
    have hIndex := successor_read_adjacent hValid hLower hRead
      (hRow.trans (congrArg (fun r => Row.bump r 0) hLowerRow.symm))
    exact ⟨upper, hIndex ▸ hRead, hRow, hShape.2.symm⟩

/-- A marked source's strict-right numerical parent is itself an actual
marker at precisely the same row. This comes from the executed weak-path
enumeration and the source's first-smaller parent, not from copied edges. -/
theorem build_marked_parent {input : List Nat} {mountain : Mountain}
    (hBuild : build input = .ok mountain)
    {root child parent : (Frame.ofMountain mountain).Node} {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref root) = .ok marked)
    (hParent : (Frame.ofMountain mountain).P child = some parent)
    (hMarked : BucketMem marked (Frame.ref child).column (Frame.ref child))
    (hRight : root.1.val < parent.1.val) :
    BucketMem marked (Frame.ref parent).column (Frame.ref parent) ∧
      (Frame.ofMountain mountain).height child = (Frame.ofMountain mountain).height parent := by
  have hNormal := build_normal_of_success hBuild
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hParentReal := Frame.real_of_value_pos hNormal.toOrdered (Frame.P_value hNormal.toOrdered hParent).1
  obtain ⟨hChildRight, low, hLowReal, hColumn, hIndex, hPath, hRow⟩ :=
    (build_markers_real_member_iff_parentPath hBuild hMarkers hReal).mp hMarked
  cases hPath with
  | refl =>
      have he := congrArg Fin.val hColumn
      omega
  | @cons child next low hNext tail =>
      have he : next = parent := Option.some.inj (hNext.symm.trans hParent)
      subst next
      have hSame : (Frame.ofMountain mountain).height parent =
          (Frame.ofMountain mountain).height child := le_antisymm
        (Frame.P_height_le hNormal.toOrdered hParent)
        (by rw [hRow]; exact tail.height_le hNormal.toOrdered)
      exact ⟨(build_markers_real_member_iff_parentPath hBuild hMarkers hParentReal).mpr
        ⟨hRight, low, hLowReal, hColumn, hIndex, tail, hSame.trans hRow⟩, hSame.symm⟩

private theorem marker_source_parent {input : List Nat} {source ambient : Mountain}
    (hBuild : build input = .ok source) {sources : Column} {references : List Ref} {shift index : Nat}
    {child parent : (Frame.ofMountain source).Node}
    (md : MarkerCopyData ambient sources references shift index)
    (hSource : source[child.1.val]? = some sources)
    (hIndex : index = child.2.val)
    (hParent : (Frame.ofMountain source).P child = some parent) :
    md.current = (Frame.ofMountain source).cell child ∧ md.sourceParent = Frame.ref parent := by
  let F := Frame.ofMountain source
  have hNormal := build_normal_of_success hBuild
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨upper, hUpper⟩ := hNormal.upper_of_parent hParent
  have hCurrent : Canonical.cellAt source (Frame.ref child) = .ok md.current :=
    cellAt_ok_iff.mpr ⟨sources, hSource, by simpa only [hIndex, Frame.ref] using md.current_at⟩
  have hUpperRef : Frame.ref upper = ⟨child.1.val, child.2.val + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  have hUpperMd : Canonical.cellAt source (Frame.ref upper) = .ok md.upper := by
    rw [hUpperRef]
    exact cellAt_ok_iff.mpr ⟨sources, hSource, by simpa only [hIndex] using md.upper_at⟩
  have hUpperCell : md.upper = F.cell upper := Except.ok.inj
    (hUpperMd.symm.trans (cellAt_of_frame_node source upper))
  obtain ⟨actualParent, hActual, _, _, hStored⟩ := hNormal.upper_step child upper hReal hUpper
  have hSame : actualParent = parent := Option.some.inj (hActual.symm.trans hParent)
  subst actualParent
  refine ⟨Except.ok.inj (hCurrent.symm.trans (cellAt_of_frame_node source child)), ?_⟩
  have hLeft := md.upper_left
  rw [hUpperCell] at hLeft
  exact Option.some.inj (hLeft.symm.trans hStored)

private theorem marked_refs_equal {mountain : Mountain}
    (hValid : MountainValid mountain) {left right : Ref} {a b : Cell}
    (hA : Canonical.cellAt mountain left = .ok a)
    (hB : Canonical.cellAt mountain right = .ok b)
    (hColumn : left.column = right.column) (hRow : a.row = b.row) : left = right := by
  obtain ⟨nodes, hNodes, hLeft⟩ := cellAt_ok_iff.mp hA
  obtain ⟨others, hOthers, hRight⟩ := cellAt_ok_iff.mp hB
  have he : others = nodes := Option.some.inj (hOthers.symm.trans (hColumn ▸ hNodes))
  subst others
  obtain ⟨hc, hNodesEq⟩ := Array.getElem?_eq_some_iff.mp hNodes
  have hCV : ColumnValid mountain left.column nodes := hNodesEq ▸ hValid _ hc
  have hIndex := column_read_index_eq_of_row hCV hLeft hRight hRow
  cases left
  cases right
  simp only [Ref.mk.injEq]
  exact ⟨hColumn, hIndex⟩

/-- Actual same-block copying carries every real weak-marker source edge
whose parent is strictly right of the bad root to an exact effective raw
edge. Both endpoint occurrences are recovered from the true current run
and prior execution history. The physical marker is not mistaken for its
raised effective endpoint. -/
theorem DynamicBlockState.actual_marker_effective_parent
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    (history : CopyRunHistory p block start references next ambient) (hLast : 1 < last)
    {child parent : (Frame.ofMountain p.reduced).Node}
    (hParent : (Frame.ofMountain p.reduced).P child = some parent)
    (hChildColumn : child.1.val = next) (hRight : p.root.column < parent.1.val)
    (hMarked : BucketMem p.marked (Frame.ref child).column (Frame.ref child))
    {column : Column}
    (hRun : copyColumn ambient p.marked references next
      (block * (p.reduced.size - 1 - p.root.column)) p.root.column = .ok column) :
    ∃ (childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column))
      (parentCopy : EffectiveCopyOccurrence p block start references parent (ambient.push column)),
      childCopy.before = ambient ∧ childCopy.column = column ∧
      childCopy.read.outputCell.row = parentCopy.read.outputCell.row ∧
      RawRefEdge (ambient.push column) childCopy.outputRef parentCopy.outputRef := by
  subst next
  let F := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.reduced_build
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hParentLeft := Frame.P_column_lt hNormal.toOrdered hParent
  obtain ⟨rootNodes, hRootNodes, hRootRead⟩ := cellAt_ok_iff.mp p.restored_root
  obtain ⟨hc, hRootEq⟩ := Array.getElem?_eq_some_iff.mp hRootNodes
  have hi : p.root.index < p.reduced[p.root.column].size := by
    rw [hRootEq]
    exact (Array.getElem?_eq_some_iff.mp hRootRead).1
  let root : F.Node := ⟨⟨p.root.column, hc⟩, ⟨p.root.index, hi⟩⟩
  have hMarkers : markers p.reduced (Frame.ref root) = .ok p.marked := p.markers_built
  obtain ⟨hParentMarked, hSourceRow⟩ :=
    build_marked_parent p.reduced_build hMarkers hParent hMarked hRight
  obtain ⟨d, hNoPremature, hParentPower, hParentLow⟩ := s.column_data hLast child.1.isLt
  have hSource : p.reduced[child.1.val]? = some d.sources :=
    (s.base_ambient child.1.val child.1.isLt).symm.trans d.source_column
  have hChildRead : d.sources[child.2.val]? = some (F.cell child) := by
    have hArray := (Array.getElem?_eq_some_iff.mp hSource).2
    rw [← hArray]
    exact Array.getElem?_eq_getElem child.2.isLt
  obtain ⟨read⟩ := d.effective_copy_read hParentPower hParentLow hNoPremature hRun hChildRead
  have hMarked' : (⟨child.1.val, child.2.val⟩ : Ref) ∈ d.bucket := hMarked
  have hIndex := read.marker_index_of_marked hMarked'
  let md := d.marker_data read.marker read.marker_mem
  obtain ⟨hCurrent, hSourceParent⟩ := marker_source_parent p.reduced_build md hSource hIndex hParent
  have hReadRow : read.outputCell.row = md.targetCell.row := by
    have hRow := read.output_row
    rw [hCurrent, Row.lift_at_root] at hRow
    exact hRow
  have hMarkerReal : 0 < read.marker.index := by
    rw [hIndex]
    exact hReal
  obtain ⟨hUpper, hRoot⟩ := d.prepared_real_marker_successor hSource read.marker_mem hMarkerReal
  obtain ⟨upper, hUpperRead, _, hLeft⟩ := d.effective_marker_upper hParentPower hParentLow
    hNoPremature hRun read.marker_mem hUpper hRoot read.output_at hReadRow
  obtain ⟨oldParentCopy⟩ := s.prior_effective_occurrence history hLast hRight hParentLeft
  have hChildReference : referenceAt start references (F.height child) = .ok read.outputCell.row :=
    (s.referenceAt_preserved (F.height child)).symm.trans (read.marked_reference hMarked')
  have hParentReference : referenceAt start references (F.height parent) =
      .ok oldParentCopy.read.outputCell.row :=
    (oldParentCopy.state.referenceAt_preserved (F.height parent)).symm.trans
      (oldParentCopy.read.marked_reference hParentMarked)
  have hChildReference' : referenceAt start references (F.height parent) = .ok read.outputCell.row := by
    change F.height child = F.height parent at hSourceRow
    simpa only [hSourceRow] using hChildReference
  have hOutputRow : read.outputCell.row = oldParentCopy.read.outputCell.row :=
    Except.ok.inj (hChildReference'.symm.trans hParentReference)
  have hTargetRead : Canonical.cellAt ambient ⟨md.sourceParent.column +
      block * (p.reduced.size - 1 - p.root.column), md.targetIndex⟩ = .ok md.targetCell :=
    cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, md.target_at⟩
  have hSelected : (⟨md.sourceParent.column + block * (p.reduced.size - 1 - p.root.column),
      md.targetIndex⟩ : Ref) = oldParentCopy.outputRef := marked_refs_equal s.ambient_valid
    hTargetRead oldParentCopy.output_read
    (by rw [hSourceParent, oldParentCopy.source_column]; rfl) (hReadRow.symm.trans hOutputRow)
  have hLeft' : upper.left = some oldParentCopy.outputRef := by
    simpa only [md, hSelected] using hLeft
  let childCopy : EffectiveCopyOccurrence p block start references child (ambient.push column) :=
    ⟨ambient, column, s, d, read, fun _ _ => rfl⟩
  let parentCopy := oldParentCopy.extend (PreservesColumns.push ambient column)
  refine ⟨childCopy, parentCopy, rfl, rfl, hOutputRow, read.outputCell, upper,
    oldParentCopy.read.outputCell, read.output_read, ?_, hLeft', parentCopy.output_read⟩
  exact cellAt_ok_iff.mpr ⟨column, by simp [childCopy, EffectiveCopyOccurrence.outputRef,
    EffectiveCopyRead.outputRef], hUpperRead⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyRead.marked_reference
#print axioms OmegaY.Expansion.ColumnCopyData.effective_marker_upper
#print axioms OmegaY.Expansion.build_marked_parent
#print axioms OmegaY.Expansion.DynamicBlockState.actual_marker_effective_parent
