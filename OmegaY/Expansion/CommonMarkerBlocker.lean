/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonMarkerBlocker.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.WeakParentPaths
import OmegaY.Expansion.ColumnCopyData
import OmegaY.Expansion.AppendLocality

/-!
# Common-parent blockers enter the same marker branch

The hypotheses refer to an actual successful source build and its actual
marker computation. Two source nodes share their numerical parent, and the
lower node's upper is strictly above the other node. No marker membership
or copied numerical-parent assertion is assumed on both nodes.
-/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem marker_parent_tail {input : List Nat} {mountain : Mountain}
    (hBuild : build input = .ok mountain)
    {root u parent : (Frame.ofMountain mountain).Node} {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref root) = .ok marked)
    (hParent : (Frame.ofMountain mountain).P u = some parent)
    (hMarker : BucketMem marked (Frame.ref u).column (Frame.ref u)) :
    ∃ low : (Frame.ofMountain mountain).Node,
      Frame.Real low ∧ low.1 = root.1 ∧ low.2.val ≤ root.2.val ∧
      Frame.ParentPath (Frame.ofMountain mountain) parent low ∧
      (Frame.ofMountain mountain).height u = (Frame.ofMountain mountain).height low ∧
      (Frame.ofMountain mountain).height parent = (Frame.ofMountain mountain).height u := by
  have hNormal := build_normal_of_success hBuild
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨hRight, low, hLowReal, hColumn, hIndex, hPath, hRow⟩ :=
    (build_markers_real_member_iff_parentPath hBuild hMarkers hReal).mp hMarker
  cases hPath with
  | refl =>
      have he := congrArg Fin.val hColumn
      omega
  | @cons u next low hNext tail =>
      have he : next = parent := Option.some.inj (hNext.symm.trans hParent)
      subst next
      refine ⟨low, hLowReal, hColumn, hIndex, tail, hRow, ?_⟩
      exact le_antisymm (Frame.P_height_le hNormal.toOrdered hParent)
        (by rw [hRow]; exact tail.height_le hNormal.toOrdered)

/-- The two actual source nodes are simultaneously marked or unmarked.
The parent is allowed to lie in the root column itself. -/
theorem build_common_parent_marker_iff {input : List Nat} {mountain : Mountain}
    (hBuild : build input = .ok mountain)
    {root u z parent zUpper : (Frame.ofMountain mountain).Node}
    {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref root) = .ok marked)
    (hUParent : (Frame.ofMountain mountain).P u = some parent)
    (hZParent : (Frame.ofMountain mountain).P z = some parent)
    (hZUpper : (Frame.ofMountain mountain).upper z = some zUpper)
    (hOrder : (Frame.ofMountain mountain).height z ≤ (Frame.ofMountain mountain).height u)
    (hBefore : (Frame.ofMountain mountain).height u < (Frame.ofMountain mountain).height zUpper)
    (hParentRight : root.1.val ≤ parent.1.val) :
    BucketMem marked (Frame.ref u).column (Frame.ref u) ↔
      BucketMem marked (Frame.ref z).column (Frame.ref z) := by
  let F := Frame.ofMountain mountain
  have hNormal : F.Normal := build_normal_of_success hBuild
  have hUReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hUParent).1.trans (Frame.P_value hNormal.toOrdered hUParent).2)
  have hZReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hZParent).1.trans (Frame.P_value hNormal.toOrdered hZParent).2)
  have hURight := hParentRight.trans_lt (Frame.P_column_lt hNormal.toOrdered hUParent)
  have hZRight := hParentRight.trans_lt (Frame.P_column_lt hNormal.toOrdered hZParent)
  constructor
  · intro hMarker
    obtain ⟨low, hLowReal, hColumn, hIndex, hTail, hRow, hParentRow⟩ :=
      marker_parent_tail hBuild hMarkers hUParent hMarker
    have hSame : F.height z = F.height u := le_antisymm hOrder
      (hParentRow ▸ Frame.P_height_le hNormal.toOrdered hZParent)
    exact (build_markers_real_member_iff_parentPath hBuild hMarkers hZReal).mpr
      ⟨hZRight, low, hLowReal, hColumn, hIndex, .cons hZParent hTail, hSame.trans hRow⟩
  · intro hMarker
    obtain ⟨low, hLowReal, hColumn, hIndex, hTail, hRow, hParentRow⟩ :=
      marker_parent_tail hBuild hMarkers hZParent hMarker
    have hUpperRow : F.height zUpper = Row.bump (F.height z) 0 := by
      have hStep := (Frame.aboveHeight_of_upper hZUpper).symm.trans (hNormal.above_row hZParent)
      rw [hParentRow, Row.B_self] at hStep
      exact hStep
    have hBefore' : F.height u < Row.bump (F.height z) 0 := by
      change F.height u < F.height zUpper at hBefore
      rw [hUpperRow] at hBefore
      exact hBefore
    have hSame : F.height u = F.height z :=
      (Row.jump_eq_zero.mp (Nat.eq_zero_of_le_zero (Row.jump_le_of_lt_bump hOrder hBefore'))).symm
    exact (build_markers_real_member_iff_parentPath hBuild hMarkers hUReal).mpr
      ⟨hURight, low, hLowReal, hColumn, hIndex, .cons hUParent hTail, hSame.trans hRow⟩

/-- In the marked branch both lower nodes and their common parent have
one row, and both source uppers are its successor. The upper nodes themselves
are obtained from source construction rather than postulated to exist. -/
theorem build_common_parent_marker_rows {input : List Nat} {mountain : Mountain}
    (hBuild : build input = .ok mountain)
    {root u z parent zUpper : (Frame.ofMountain mountain).Node}
    {marked : Array (List Ref)}
    (hMarkers : markers mountain (Frame.ref root) = .ok marked)
    (hUParent : (Frame.ofMountain mountain).P u = some parent)
    (hZParent : (Frame.ofMountain mountain).P z = some parent)
    (hZUpper : (Frame.ofMountain mountain).upper z = some zUpper)
    (hOrder : (Frame.ofMountain mountain).height z ≤ (Frame.ofMountain mountain).height u)
    (hBefore : (Frame.ofMountain mountain).height u < (Frame.ofMountain mountain).height zUpper)
    (hParentRight : root.1.val ≤ parent.1.val)
    (hMarked : BucketMem marked (Frame.ref u).column (Frame.ref u) ∨
      BucketMem marked (Frame.ref z).column (Frame.ref z)) :
    BucketMem marked (Frame.ref u).column (Frame.ref u) ∧
    BucketMem marked (Frame.ref z).column (Frame.ref z) ∧
    (Frame.ofMountain mountain).height u = (Frame.ofMountain mountain).height parent ∧
    (Frame.ofMountain mountain).height z = (Frame.ofMountain mountain).height parent ∧
    ∃ uUpper, (Frame.ofMountain mountain).upper u = some uUpper ∧
      (Frame.ofMountain mountain).height uUpper = Row.bump ((Frame.ofMountain mountain).height parent) 0 ∧
      (Frame.ofMountain mountain).height zUpper = Row.bump ((Frame.ofMountain mountain).height parent) 0 := by
  have hNormal := build_normal_of_success hBuild
  have hIff := build_common_parent_marker_iff hBuild hMarkers hUParent hZParent hZUpper hOrder hBefore hParentRight
  have hU := hMarked.elim id hIff.mpr
  have hZ := hIff.mp hU
  obtain ⟨_, _, _, _, _, _, hURow⟩ := marker_parent_tail hBuild hMarkers hUParent hU
  obtain ⟨_, _, _, _, _, _, hZRow⟩ := marker_parent_tail hBuild hMarkers hZParent hZ
  obtain ⟨uUpper, hUUpper⟩ := hNormal.upper_of_parent hUParent
  refine ⟨hU, hZ, hURow.symm, hZRow.symm, uUpper, hUUpper, ?_, ?_⟩
  · exact (Frame.aboveHeight_of_upper hUUpper).symm.trans
      ((hNormal.above_row hUParent).trans (by rw [← hURow, Row.B_self]))
  · exact (Frame.aboveHeight_of_upper hZUpper).symm.trans
      ((hNormal.above_row hZParent).trans (by rw [← hZRow, Row.B_self]))

private theorem markerCopyData_source {input : List Nat} {source ambient : Mountain}
    (hBuild : build input = .ok source) {sources : Column} {references : List Ref} {shift : Nat}
    {u parent : (Frame.ofMountain source).Node}
    (md : MarkerCopyData ambient sources references shift u.2.val)
    (hSource : source[u.1.val]? = some sources)
    (hParent : (Frame.ofMountain source).P u = some parent) :
    md.current = (Frame.ofMountain source).cell u ∧ md.sourceParent = Frame.ref parent := by
  let F := Frame.ofMountain source
  have hNormal : F.Normal := build_normal_of_success hBuild
  have hReal := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨upper, hUpper⟩ := hNormal.upper_of_parent hParent
  have hCurrent : Canonical.cellAt source (Frame.ref u) = .ok md.current :=
    Canonical.cellAt_ok_iff.mpr ⟨sources, hSource, md.current_at⟩
  have hUpperRef : Frame.ref upper = ⟨u.1.val, u.2.val + 1⟩ := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩
  have hUpperMd : Canonical.cellAt source (Frame.ref upper) = .ok md.upper := by
    rw [hUpperRef]
    exact Canonical.cellAt_ok_iff.mpr ⟨sources, hSource, md.upper_at⟩
  have hUpperCell : md.upper = F.cell upper := Except.ok.inj
    (hUpperMd.symm.trans (Canonical.cellAt_of_frame_node source upper))
  obtain ⟨actualParent, hActual, _, _, hStored⟩ := hNormal.upper_step u upper hReal hUpper
  have hParentEq : actualParent = parent := Option.some.inj (hActual.symm.trans hParent)
  subst actualParent
  refine ⟨Except.ok.inj (hCurrent.symm.trans (Canonical.cellAt_of_frame_node source u)), ?_⟩
  exact Option.some.inj (md.upper_left.symm.trans (by simpa only [hUpperCell] using hStored))

/-- Input data for two different copy times select the same full parent
column and the same reference target. The ambient mountains may differ;
actual complete-column preservation, including the block-start references,
supplies selector stability. This does not require a copied normal graph. -/
theorem build_common_parent_marker_data {input : List Nat} {source before after : Mountain}
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
    (hMarked : BucketMem marked (Frame.ref u).column (Frame.ref u) ∨
      BucketMem marked (Frame.ref z).column (Frame.ref z))
    {uSources zSources : Column}
    (du : MarkerCopyData after uSources references shift u.2.val)
    (dz : MarkerCopyData before zSources references shift z.2.val)
    (hUSource : source[u.1.val]? = some uSources)
    (hZSource : source[z.1.val]? = some zSources)
    (hValid : MountainValid before) (hPreserve : PreservesColumns before after)
    (hRefs : ∀ ref ∈ references, ValidRef before ref) :
    du.sourceParent = Frame.ref parent ∧ dz.sourceParent = Frame.ref parent ∧
    du.current.row = dz.current.row ∧
    du.parentNodes = dz.parentNodes ∧ du.targetIndex = dz.targetIndex ∧
    du.targetCell = dz.targetCell := by
  obtain ⟨_, _, hURow, hZRow, _⟩ := build_common_parent_marker_rows hBuild hMarkers
    hUParent hZParent hZUpper hOrder hBefore hParentRight hMarked
  obtain ⟨hUCell, hURef⟩ := markerCopyData_source hBuild du hUSource hUParent
  obtain ⟨hZCell, hZRef⟩ := markerCopyData_source hBuild dz hZSource hZParent
  have hRows : du.current.row = dz.current.row := by
    rw [hUCell, hZCell]
    exact hURow.trans hZRow.symm
  have hTargetRows : du.targetCell.row = dz.targetCell.row := Except.ok.inj
    (du.reference.symm.trans ((hPreserve.referenceAt hRefs du.current.row).trans
      (by rw [hRows]; exact dz.reference)))
  have hParentCol : du.sourceParent.column + shift = dz.sourceParent.column + shift := by
    rw [hURef, hZRef]
  have hColBound := (Array.getElem?_eq_some_iff.mp dz.parent_nodes).1
  have hColumn : du.parentNodes = dz.parentNodes := Option.some.inj
    (du.parent_nodes.symm.trans (by rw [hParentCol]; exact (hPreserve _ hColBound).trans dz.parent_nodes))
  have hZTarget : du.parentNodes[dz.targetIndex]? = some dz.targetCell := by
    rw [hColumn]
    exact dz.target_at
  have hColumnValid : ColumnValid before (dz.sourceParent.column + shift) dz.parentNodes := by
    obtain ⟨hc, he⟩ := Array.getElem?_eq_some_iff.mp dz.parent_nodes
    exact he ▸ hValid _ hc
  have hStrict : FillRowsStrict du.parentNodes := by
    rw [hColumn]
    exact hColumnValid.rows_strict
  have hIndex : du.targetIndex = dz.targetIndex := by
    rcases lt_trichotomy du.targetIndex dz.targetIndex with hlt | heq | hgt
    · exact False.elim ((not_lt_of_ge hTargetRows.ge)
        (hStrict _ _ _ _ du.target_at hZTarget hlt))
    · exact heq
    · exact False.elim ((not_lt_of_ge hTargetRows.le)
        (hStrict _ _ _ _ hZTarget du.target_at hgt))
  have hTarget : du.targetCell = dz.targetCell := Option.some.inj
    (du.target_at.symm.trans (by rw [hIndex]; exact hZTarget))
  exact ⟨hURef, hZRef, hRows, hColumn, hIndex, hTarget⟩

/-- Both actual fill calls produce exactly one common list of cells,
including its stored parent references. Different incoming legs of the
physical markers are irrelevant: `fill` reads their source uppers.
Successful fills are conclusions, not assumptions. -/
theorem build_common_parent_marker_fill {input : List Nat} {source before after : Mountain}
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
    (hMarked : BucketMem marked (Frame.ref u).column (Frame.ref u) ∨
      BucketMem marked (Frame.ref z).column (Frame.ref z))
    {uSources zSources : Column}
    (du : MarkerCopyData after uSources references shift u.2.val)
    (dz : MarkerCopyData before zSources references shift z.2.val)
    (hUSource : source[u.1.val]? = some uSources)
    (hZSource : source[z.1.val]? = some zSources)
    (hUAmbient : after[u.1.val]? = some uSources)
    (hZAmbient : before[z.1.val]? = some zSources)
    (hValid : MountainValid before) (hPreserve : PreservesColumns before after)
    (hRefs : ∀ ref ∈ references, ValidRef before ref) :
    ∃ gap : List Cell,
      fill after ⟨u.1.val, u.2.val + 1⟩ shift du.current.row du.targetCell.row = .ok gap ∧
      fill before ⟨z.1.val, z.2.val + 1⟩ shift dz.current.row dz.targetCell.row = .ok gap := by
  obtain ⟨hURef, hZRef, hRows, hColumn, _, hTarget⟩ :=
    build_common_parent_marker_data hBuild hMarkers hUParent hZParent hZUpper hOrder hBefore
      hParentRight hMarked du dz hUSource hZSource hValid hPreserve hRefs
  have hNormal := build_normal_of_success hBuild
  have hParentEq : du.sourceParent = dz.sourceParent := hURef.trans hZRef.symm
  have hColumnValid : ColumnValid before (dz.sourceParent.column + shift) dz.parentNodes := by
    obtain ⟨hc, he⟩ := Array.getElem?_eq_some_iff.mp dz.parent_nodes
    exact he ▸ hValid _ hc
  have hStrictZ : FillRowsStrict dz.parentNodes := hColumnValid.rows_strict
  have hStrictU : FillRowsStrict du.parentNodes := by rw [hColumn]; exact hStrictZ
  have hLeftU : du.sourceParent.column + shift < u.1.val + shift := by
    rw [hURef]
    exact Nat.add_lt_add_right (Frame.P_column_lt hNormal.toOrdered hUParent) shift
  have hLeftZ : dz.sourceParent.column + shift < z.1.val + shift := by
    rw [hZRef]
    exact Nat.add_lt_add_right (Frame.P_column_lt hNormal.toOrdered hZParent) shift
  have hFillU := fill_eq_cells
    (source := ⟨u.1.val, u.2.val + 1⟩)
    (lookup_ok_iff.mpr (show CellAt after ⟨u.1.val, u.2.val + 1⟩ du.upper from
      ⟨uSources, hUAmbient, du.upper_at⟩))
    du.upper_left du.parent_nodes hStrictU du.target_at le_rfl hLeftU
    (low := du.current.row)
  have hFillZ := fill_eq_cells
    (source := ⟨z.1.val, z.2.val + 1⟩)
    (lookup_ok_iff.mpr (show CellAt before ⟨z.1.val, z.2.val + 1⟩ dz.upper from
      ⟨zSources, hZAmbient, dz.upper_at⟩))
    dz.upper_left dz.parent_nodes hStrictZ dz.target_at le_rfl hLeftZ
    (low := dz.current.row)
  have hGap : fillCells dz.parentNodes (dz.sourceParent.column + shift)
      dz.current.row dz.targetCell.row =
      fillCells du.parentNodes (du.sourceParent.column + shift) du.current.row du.targetCell.row := by
    rw [← hColumn, ← hParentEq, ← hRows, ← hTarget]
  exact ⟨_, hFillU, hFillZ.trans (congrArg Except.ok hGap)⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_common_parent_marker_iff
#print axioms OmegaY.Expansion.build_common_parent_marker_rows
#print axioms OmegaY.Expansion.build_common_parent_marker_data
#print axioms OmegaY.Expansion.build_common_parent_marker_fill
