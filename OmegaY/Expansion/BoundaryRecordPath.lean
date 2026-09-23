/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/BoundaryRecordPath.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FillRecordPath
import OmegaY.Expansion.FillContourSeam
import OmegaY.Expansion.ReducedHighTail
import OmegaY.Expansion.ExactRootCap
import OmegaY.Expansion.PreparedColumnData

/-!
# Actual boundary seeds and fill-cap record subdivisions

The highest initial reference is derived from the executed decrement graft,
not from an assumed record history. Its stored parent is the original bad
root's parent, when that parent exists. A raised fill cap then gives a real
additional edge to its selected parent-column reference. These facts address
the highest root interval; lower root intervals still need cut-path transfer.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- The old penultimate node, after the actual decrement, is exactly the
initial selector below the old last top. Its upper is the copied original
root upper, so its raw parent is the original root's parent. -/
theorem Preparation.initial_badRoot_reference_edge {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (g : RootGeometry p)
    {parent : (Frame.ofMountain p.initial).Node}
    (hParent : (Frame.ofMountain p.initial).P g.rootNode = some parent) :
    ∃ lower : (Frame.ofMountain p.reduced).Node,
      below p.reduced (p.reduced.size - 1) p.lastTop.row = .ok (Frame.ref lower) ∧
      lower.1.val = p.reduced.size - 1 ∧
      RawRefEdge p.reduced (Frame.ref lower) (Frame.ref parent) ∧
      Canonical.cellAt p.reduced (Frame.ref parent) = .ok ((Frame.ofMountain p.initial).cell parent) ∧
      p.rootCell.row ≤ (Frame.ofMountain p.reduced).height lower ∧
      (Frame.ofMountain p.reduced).height lower < p.lastTop.row := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hNormal : F.Normal := build_normal_of_success p.initial_build
  obtain ⟨rootUpper, hRootUpper⟩ := hNormal.upper_of_parent hParent
  obtain ⟨lower, hRef, hCell, hTail⟩ := p.reduced_exact_root_suffix hLast g
  have hLowerRow : G.height lower = F.height g.lower := by
    change (G.cell lower).row = _
    rw [hCell, decCell_row]
    rfl
  obtain ⟨upper, hUpper, hUpperCell⟩ : ∃ upper : G.Node,
      G.upper lower = some upper ∧ G.cell upper = F.cell rootUpper := by
    cases hUpper : G.upper lower with
    | none =>
        rw [upperSuffix_of_upper_none hUpper, upperSuffix_of_upper hRootUpper] at hTail
        cases hTail
    | some upper =>
        rw [upperSuffix_of_upper hUpper, upperSuffix_of_upper hRootUpper] at hTail
        exact ⟨upper, rfl, (List.cons.inj hTail).1⟩
  have hRootParentLeft : parent.1.val < p.root.column := by
    have hc := Frame.P_column_lt hNormal.toOrdered hParent
    simpa only [show g.rootNode.1.val = p.root.column from congrArg Ref.column g.root_ref] using hc
  have hParentRead : Canonical.cellAt p.reduced (Frame.ref parent) = .ok (F.cell parent) := by
    rw [← build_changed_last_preserves_ref p.initial_build p.reduced_build
      (ref := Frame.ref parent) (hRootParentLeft.trans p.root_before_last)]
    exact Canonical.cellAt_of_frame_node p.initial parent
  obtain ⟨parentReduced, hParentRef, hParentCell⟩ := Canonical.frame_node_of_cellAt hParentRead
  obtain ⟨actualParent, hActualParent, _, _, hRootLeft⟩ :=
    hNormal.upper_step g.rootNode rootUpper g.root_real hRootUpper
  have hActualEq : actualParent = parent := Option.some.inj (hActualParent.symm.trans hParent)
  subst actualParent
  have hRaw : G.rawParent lower = some parentReduced := by
    apply Frame.rawParent_eq_of_upper_left hUpper
    simpa only [hUpperCell, hParentRef] using hRootLeft
  have hEdge : RawRefEdge p.reduced (Frame.ref lower) (Frame.ref parent) := by
    simpa only [hParentRef] using RawRefEdge.of_rawParent hRaw
  have hUpperBound : p.lastTop.row ≤ G.height upper := by
    have hD := Frame.father_upper_bound_nodes hNormal g.lower_parent g.lower_upper hRootUpper
    change (F.cell g.topNode).row ≤ (F.cell rootUpper).row at hD
    have hTop : F.cell g.topNode = p.lastTop := g.top_cell
    rw [hTop] at hD
    change (p.lastTop).row ≤ (G.cell upper).row
    rw [hUpperCell]
    exact hD
  have hColumn : lower.1.val = p.reduced.size - 1 := by
    have hc : lower.1.val = g.lower.1.val := congrArg Ref.column hRef
    have hs := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hs
    rw [hc, g.lower_column]
    omega
  have hUpperRead : p.reduced[lower.1.val][lower.2.val + 1]? = some (G.cell upper) := by
    have hUpperRef : Frame.ref upper = ⟨lower.1.val, lower.2.val + 1⟩ := by
      simp only [Frame.ref, Ref.mk.injEq]
      exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
    have hFull : Canonical.cellAt p.reduced ⟨lower.1.val, lower.2.val + 1⟩ = .ok (G.cell upper) := by
      rw [← hUpperRef]
      exact Canonical.cellAt_of_frame_node p.reduced upper
    obtain ⟨nodes, hNodes, hRead⟩ := Canonical.cellAt_ok_iff.mp hFull
    have hNodeEq : nodes = p.reduced[lower.1.val] := Option.some.inj
      (hNodes.symm.trans (Array.getElem?_eq_getElem lower.1.isLt))
    simpa only [hNodeEq] using hRead
  have hBelow := below_eq_of_adjacent p.reduced_valid
    (Array.getElem?_eq_getElem lower.1.isLt) (Array.getElem?_eq_getElem lower.2.isLt)
    hUpperRead (show G.height lower < p.lastTop.row by rw [hLowerRow]; exact g.lower_lt_top)
    hUpperBound
  refine ⟨lower, ?_, hColumn, hEdge, hParentRead, ?_, ?_⟩
  · simpa only [Frame.ref, hColumn] using hBelow
  · rw [hLowerRow]
    exact g.root_le_lower
  · rw [hLowerRow]
    exact g.lower_lt_top

/-- The literal initial reference map selects the same grafted node when
queried at the bad-root row. The cap is proved to be Z from its actual
boundary-list membership, rather than assumed from a sufficient interval. -/
theorem Preparation.initial_badRoot_reference_query_edge {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (g : RootGeometry p)
    {parent : (Frame.ofMountain p.initial).Node}
    (hParent : (Frame.ofMountain p.initial).P g.rootNode = some parent)
    {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∃ lower : (Frame.ofMountain p.reduced).Node,
      below p.reduced (p.reduced.size - 1) p.lastTop.row = .ok (Frame.ref lower) ∧
      lower.1.val = p.reduced.size - 1 ∧
      referenceAt p.reduced references p.rootCell.row = .ok ((Frame.ofMountain p.reduced).height lower) ∧
      RawRefEdge p.reduced (Frame.ref lower) (Frame.ref parent) ∧
      Canonical.cellAt p.reduced (Frame.ref parent) = .ok ((Frame.ofMountain p.initial).cell parent) := by
  obtain ⟨lower, hBelow, hColumn, hEdge, hParentRead, _, _⟩ :=
    p.initial_badRoot_reference_edge hLast g hParent
  obtain ⟨nodes, hNodes, hRoot⟩ := Canonical.cellAt_ok_iff.mp p.initial_root
  obtain ⟨ceiling, degree, ref, cell, hMem, _, _, hSelected, hRead, _, hQuery, hLow, hHigh, _⟩ :=
    RootRowsInColumn.root_interval_with_boundary (p.reduced_root_rows hLast)
      p.reduced_valid hLast hNodes hRoot le_rfl hMap
  have hCap : ceiling = p.lastTop.row := p.boundary_cap_eq_lastTop hNodes hMem (hLow.trans_lt hHigh)
  rw [hCap] at hSelected
  have hRef : ref = Frame.ref lower := Except.ok.inj (hSelected.symm.trans hBelow)
  have hCell : cell = (Frame.ofMountain p.reduced).cell lower := Except.ok.inj
    (hRead.symm.trans (by rw [hRef]; exact Canonical.cellAt_of_frame_node p.reduced lower))
  exact ⟨lower, hBelow, hColumn, by simpa only [hCell, Frame.height] using hQuery, hEdge, hParentRead⟩

/-- Any actual cap seam may extend an already constructed path. The new
edge is derived from real fill/contour adjacency, not supplied as a premise. -/
theorem ColumnCopyData.prepared_fill_cap_extend_path {front : List Nat} {last : Nat}
    {p : Preparation front last} {mountain : Mountain} {references : List Ref}
    {sourceColumn shift : Nat}
    (d : ColumnCopyData mountain p.marked references sourceColumn shift p.root.column)
    (hSource : p.reduced[sourceColumn]? = some d.sources)
    (hParentPower : ∀ marker (hm : marker ∈ d.bucket), ColumnPowerSteps (d.marker_data marker hm).parentNodes)
    (hParentLow : ∀ marker (hm : marker ∈ d.bucket), ∃ (i : Nat) (cell : Cell),
      (d.marker_data marker hm).parentNodes[i]? = some cell ∧ cell.row = (d.marker_data marker hm).current.row)
    (hNoPremature : NoPrematureOne d.sources) {column : Column}
    (hRun : copyColumn mountain p.marked references sourceColumn shift p.root.column = .ok column)
    {marker : Ref} (hm : marker ∈ d.bucket)
    (hRaised : (d.marker_data marker hm).current.row < (d.marker_data marker hm).targetCell.row)
    {sourceParent : Ref}
    (hPath : RawRefPath mountain
      ⟨(d.marker_data marker hm).sourceParent.column + shift, (d.marker_data marker hm).targetIndex⟩ sourceParent) :
    ∃ index cell, column[index]? = some cell ∧ 0 < index ∧
      cell.row = (d.marker_data marker hm).targetCell.row ∧
      RawRefPath (mountain.push column) ⟨mountain.size, index⟩ sourceParent := by
  obtain ⟨step, hRow, _⟩ := d.prepared_fill_contour_seam hSource hParentPower hParentLow
    hNoPremature hRun hm hRaised
  have hEdge : RawRefEdge (mountain.push column) ⟨mountain.size, step.position⟩
      ⟨(d.marker_data marker hm).sourceParent.column + shift, (d.marker_data marker hm).targetIndex⟩ := by
    refine ⟨step.lower, step.upper, _, ?_, ?_, step.upper_left, step.parent_at⟩
    · exact Canonical.cellAt_ok_iff.mpr ⟨column, by simp, step.lower_at⟩
    · exact Canonical.cellAt_ok_iff.mpr ⟨column, by simp, step.upper_at⟩
  exact ⟨step.position, step.lower, step.lower_at, step.position_positive, hRow,
    .cons hEdge (hPath.preserve (PreservesColumns.push mountain column))⟩

private theorem prepared_marker_parent_row {front : List Nat} {last : Nat}
    {p : Preparation front last} {references : List Ref} {sourceColumn shift : Nat}
    (d : ColumnCopyData p.reduced p.marked references sourceColumn shift p.root.column)
    {marker : Ref} (hm : marker ∈ d.bucket) :
    ∃ parent, Canonical.cellAt p.reduced (d.marker_data marker hm).sourceParent = .ok parent ∧
      parent.row = (d.marker_data marker hm).current.row := by
  let md := d.marker_data marker hm
  obtain ⟨_, parent, current, upper, parentCell, _, hCurrent, hUpper, hLeft, _, hParent, hParentRow, _⟩ :=
    markers_upper_parent
      (weakLocal_of_ordered p.reduced_valid.toOrdered p.reduced_valid.left_sources)
      p.root_valid p.markers_built hm
  have hCurrentMd : Canonical.cellAt p.reduced marker = .ok md.current :=
    Canonical.cellAt_ok_iff.mpr ⟨d.sources,
      by simpa only [d.marker_columns marker hm] using d.source_column, md.current_at⟩
  have hUpperMd : Canonical.cellAt p.reduced ⟨marker.column, marker.index + 1⟩ = .ok md.upper :=
    Canonical.cellAt_ok_iff.mpr ⟨d.sources,
      by simpa only [d.marker_columns marker hm] using d.source_column, md.upper_at⟩
  have hCurrentEq : current = md.current := Except.ok.inj ((Canonical.cellAt_ok_iff.mpr hCurrent).symm.trans hCurrentMd)
  have hUpperEq : upper = md.upper := Except.ok.inj ((Canonical.cellAt_ok_iff.mpr hUpper).symm.trans hUpperMd)
  have hParentEq : parent = md.sourceParent := Option.some.inj
    (hLeft.symm.trans (by simpa only [hUpperEq] using md.upper_left))
  exact ⟨parentCell, by simpa only [hParentEq] using Canonical.cellAt_ok_iff.mpr hParent,
    by simpa only [hCurrentEq] using hParentRow⟩

/-- A complete actual highest-root subdivision in the first copied column.
The source marker's stored endpoint is the bad root; all copy data, fill
support and the initial reference path are derived from preparation. The
two output edges end at the original bad root's numerical parent. There is
no record-history, copied-normality, or desired path premise. -/
theorem Preparation.first_badRoot_fill_subdivision {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references)
    {column : Column}
    (hRun : copyColumn p.reduced p.marked references (p.root.column + 1)
      (p.reduced.size - 1 - p.root.column) p.root.column = .ok column)
    {marker : Ref} (hMarker : BucketMem p.marked (p.root.column + 1) marker)
    {sourceUpper : Cell}
    (hUpperRead : Canonical.cellAt p.reduced ⟨marker.column, marker.index + 1⟩ = .ok sourceUpper)
    (hUpperLeft : sourceUpper.left = some p.root)
    {parent : (Frame.ofMountain p.initial).Node}
    (hSourceParent : Canonical.findParent p.initial p.root = .ok (Frame.ref parent))
    {target : Row}
    (hReference : referenceAt p.reduced references p.rootCell.row = .ok target)
    (hRaised : p.rootCell.row < target) :
    ∃ index cell, column[index]? = some cell ∧ 0 < index ∧ cell.row = target ∧
      RawRefPath (p.reduced.push column) ⟨p.reduced.size, index⟩ (Frame.ref parent) ∧
      Canonical.cellAt (p.reduced.push column) (Frame.ref parent) =
        .ok ((Frame.ofMountain p.initial).cell parent) := by
  let G := Frame.ofMountain p.reduced
  obtain ⟨g⟩ := p.root_geometry hLast
  have hRootParent : (Frame.ofMountain p.initial).P g.rootNode = some parent := by
    apply (Executable.findParent_ref_iff (build_normal_of_success p.initial_build).toOrdered g.rootNode parent).mp
    simpa only [g.root_ref] using hSourceParent
  obtain ⟨lower, _, hLowerColumn, hQuery, hEdge, hParentRead⟩ :=
    p.initial_badRoot_reference_query_edge hLast g hRootParent hMap
  obtain ⟨d, hPP, hPL⟩ := p.first_column_copy_data_with_parent_rows hLast hMap
  let md := d.marker_data marker hMarker
  have hUpperMd : Canonical.cellAt p.reduced ⟨marker.column, marker.index + 1⟩ = .ok md.upper :=
    Canonical.cellAt_ok_iff.mpr ⟨d.sources,
      by simpa only [d.marker_columns marker hMarker] using d.source_column, md.upper_at⟩
  have hUpperEq : md.upper = sourceUpper := Except.ok.inj (hUpperMd.symm.trans hUpperRead)
  have hSourceRoot : md.sourceParent = p.root := Option.some.inj
    (md.upper_left.symm.trans (by simpa only [hUpperEq] using hUpperLeft))
  obtain ⟨sourceParent, hSourceParentRead, hSourceParentRow⟩ := prepared_marker_parent_row d hMarker
  have hSourceParentCell : sourceParent = p.rootCell := by
    have hRootRead : Canonical.cellAt p.reduced (d.marker_data marker hMarker).sourceParent = .ok p.rootCell := by
      rw [show (d.marker_data marker hMarker).sourceParent = p.root from hSourceRoot]
      exact p.restored_root
    exact Except.ok.inj (hSourceParentRead.symm.trans hRootRead)
  have hCurrentRoot : md.current.row = p.rootCell.row := by
    simpa only [hSourceParentCell] using hSourceParentRow.symm
  have hTarget : md.targetCell.row = target := Except.ok.inj
    (md.reference.symm.trans (by rw [hCurrentRoot]; exact hReference))
  have hLowerTarget : G.height lower = target := Except.ok.inj (hQuery.symm.trans hReference)
  let targetRef : Ref := ⟨md.sourceParent.column + (p.reduced.size - 1 - p.root.column), md.targetIndex⟩
  have hTargetRead : Canonical.cellAt p.reduced targetRef = .ok md.targetCell :=
    Canonical.cellAt_ok_iff.mpr ⟨md.parentNodes, md.parent_nodes, md.target_at⟩
  obtain ⟨targetNode, hTargetRef, hTargetCell⟩ := Canonical.frame_node_of_cellAt hTargetRead
  have hBoundaryIndex : targetRef.column = p.reduced.size - 1 := by
    have hDest := d.destination
    dsimp only [targetRef]
    rw [hSourceRoot]
    omega
  have hSameColumn : targetNode.1 = lower.1 := Fin.ext (by
    have hh : targetNode.1.val = targetRef.column := congrArg Ref.column hTargetRef
    exact hh.trans (hBoundaryIndex.trans hLowerColumn.symm))
  have hSameRow : G.height targetNode = G.height lower := by
    change (G.cell targetNode).row = _
    rw [hTargetCell]
    exact hTarget.trans hLowerTarget.symm
  have hTargetNode : targetNode = lower := Frame.node_eq_of_column_height p.reduced_valid.toOrdered hSameColumn hSameRow
  have hTargetRefEq : targetRef = Frame.ref lower := hTargetRef.symm.trans (congrArg Frame.ref hTargetNode)
  have hInitialPath : RawRefPath p.reduced targetRef (Frame.ref parent) := by
    rw [hTargetRefEq]
    exact .cons hEdge (.refl _)
  obtain ⟨index, cell, hCell, hReal, hRow, hPath⟩ := d.prepared_fill_cap_extend_path
    d.source_column hPP hPL (build_source_no_premature_one p.reduced_build d.source_column)
    hRun hMarker (by change md.current.row < md.targetCell.row; rw [hCurrentRoot, hTarget]; exact hRaised)
    hInitialPath
  have hParentReadNew : Canonical.cellAt (p.reduced.push column) (Frame.ref parent) =
      .ok ((Frame.ofMountain p.initial).cell parent) := by
    obtain ⟨nodes, hNodes, _⟩ := Canonical.cellAt_ok_iff.mp hParentRead
    rw [Canonical.cellAt_push_left (Array.getElem?_eq_some_iff.mp hNodes).1]
    exact hParentRead
  exact ⟨index, cell, hCell, hReal, hRow.trans hTarget, hPath, hParentReadNew⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_badRoot_reference_edge
#print axioms OmegaY.Expansion.Preparation.initial_badRoot_reference_query_edge
#print axioms OmegaY.Expansion.ColumnCopyData.prepared_fill_cap_extend_path
#print axioms OmegaY.Expansion.Preparation.first_badRoot_fill_subdivision
