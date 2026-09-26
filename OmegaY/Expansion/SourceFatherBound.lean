/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/SourceFatherBound.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawFatherBound
import OmegaY.Expansion.ActualRootInterval

/-! Source father-upper bounds transferred through actual complete column
preservation. The copied cell's row must still be identified with the source
row; an arbitrary raised query does not satisfy this interface. -/

namespace OmegaY.Geometry.Frame

theorem upper_of_refs {F : Frame} {before after : F.Node} {column index : Nat}
    (hBefore : ref before = ⟨column, index⟩)
    (hAfter : ref after = ⟨column, index + 1⟩) : F.upper before = some after := by
  rcases before with ⟨c, i⟩
  rcases after with ⟨d, j⟩
  simp only [ref, Canonical.Ref.mk.injEq] at hBefore hAfter
  have hc : d = c := Fin.ext (hAfter.1.trans hBefore.1.symm)
  subst d
  have hBound : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [upper, hBound, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [ref, Canonical.Ref.mk.injEq]
  exact ⟨trivial, by omega⟩

theorem index_gt_one_of_height_gt_one {F : Frame} (hF : F.Ordered)
    {u : F.Node} (hAbove : (1 : Row) < F.height u) : 1 < u.2.val := by
  rcases u with ⟨c, i⟩
  change 1 < i.val
  by_contra h
  have hIndex : i.val = 0 ∨ i.val = 1 := by omega
  rcases hIndex with hi | hi
  · have hZero : i = ⟨0, by have := i.isLt; omega⟩ := Fin.ext hi
    simp only [height, cell, hZero, hF.phantom, Canonical.phantom] at hAbove
    exact (not_lt_of_ge (Row.zero_le 1)) hAbove
  · have hOne : i = ⟨1, by have := i.isLt; omega⟩ := Fin.ext hi
    simp only [height, cell, hOne, hF.bottom_row, lt_self_iff_false] at hAbove

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- An upper stored endpoint in a real canonical source obeys the father
upper bound at its actual array reference. -/
theorem build_stored_parent_upper_bound {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain)
    {source : Ref} {cell parentUpper : Cell} {parentRef : Ref}
    (hCell : Canonical.cellAt mountain source = .ok cell)
    (hAbove : (1 : Row) < cell.row) (hLeft : cell.left = some parentRef)
    (hParentUpper : Canonical.cellAt mountain ⟨parentRef.column, parentRef.index + 1⟩ =
      .ok parentUpper) : cell.row ≤ parentUpper.row := by
  let F := Frame.ofMountain mountain
  have hNormal := build_normal_of_success hBuild
  obtain ⟨upper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hCell
  have hIndex : 1 < upper.2.val := Frame.index_gt_one_of_height_gt_one hNormal.toOrdered
    (by simpa only [Frame.height, hUpperCell] using hAbove)
  let child : F.Node := ⟨upper.1, ⟨upper.2.val - 1,
    (Nat.sub_le _ _).trans_lt upper.2.isLt⟩⟩
  have hReal : Frame.Real child := by change 0 < upper.2.val - 1; omega
  have hUpper : F.upper child = some upper := by
    apply Frame.upper_of_refs (rfl : Frame.ref child =
      ⟨upper.1.val, upper.2.val - 1⟩)
    change Frame.ref upper = ⟨upper.1.val, upper.2.val - 1 + 1⟩
    simp only [Frame.ref, Nat.sub_add_cancel (by omega : 1 ≤ upper.2.val)]
  obtain ⟨parent, hLookup, _, _⟩ := hNormal.toOrdered.stored_valid upper parentRef
    (by simpa only [hUpperCell] using hLeft)
  have hParentRef : Frame.ref parent = parentRef := Frame.lookup_spec hLookup
  have hRaw : F.rawParent child = some parent := Frame.rawParent_eq_of_upper_left hUpper
    (by simpa only [F, hUpperCell, hParentRef] using hLeft)
  obtain ⟨fatherUpper, hFatherRef, hFatherCell⟩ := Canonical.frame_node_of_cellAt hParentUpper
  have hFatherUpper : F.upper parent = some fatherUpper :=
    Frame.upper_of_refs hParentRef hFatherRef
  have hBound := hNormal.rawFatherUpperBound child parent upper fatherUpper hReal hRaw hUpper hFatherUpper
  simpa only [Frame.height, hUpperCell, hFatherCell] using hBound

/-- A preserved parent column retains its actual immediate upper index.
This transfers the source bound to the ambient copy state. -/
theorem DynamicBlockState.fixed_source_parent_upper_bound
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    {source : Ref} {cell parentUpper : Cell} {parentRef : Ref}
    (hCell : Canonical.cellAt p.reduced source = .ok cell)
    (hAbove : (1 : Row) < cell.row) (hLeft : cell.left = some parentRef)
    (hFixed : parentRef.column < p.root.column)
    (hParentUpper : Canonical.cellAt ambient ⟨parentRef.column, parentRef.index + 1⟩ =
      .ok parentUpper) : cell.row ≤ parentUpper.row := by
  have hBefore : parentRef.column < p.reduced.size := by
    have := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at this
    have := p.root_before_last
    omega
  have hRead : Canonical.cellAt p.reduced ⟨parentRef.column, parentRef.index + 1⟩ =
      .ok parentUpper :=
    (cellAt_eq_of_column_eq (ref := ⟨parentRef.column, parentRef.index + 1⟩)
      (s.base_ambient parentRef.column hBefore)).symm.trans hParentUpper
  exact build_stored_parent_upper_bound p.reduced_build hCell hAbove hLeft hRead

/-- Bottom and phantom rows also satisfy the stored upper bound, since any
referenced successor is a real row and therefore at least one. -/
theorem build_stored_parent_upper_bound_all {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain)
    {source : Ref} {cell parentUpper : Cell} {parentRef : Ref}
    (hCell : Canonical.cellAt mountain source = .ok cell)
    (hLeft : cell.left = some parentRef)
    (hParentUpper : Canonical.cellAt mountain ⟨parentRef.column, parentRef.index + 1⟩ =
      .ok parentUpper) : cell.row ≤ parentUpper.row := by
  by_cases hAbove : (1 : Row) < cell.row
  · exact build_stored_parent_upper_bound hBuild hCell hAbove hLeft hParentUpper
  · obtain ⟨upper, hRef, hCellEq⟩ := Canonical.frame_node_of_cellAt hParentUpper
    have hReal : Frame.Real upper := by
      have hIndex := congrArg Ref.index hRef
      change upper.2.val = parentRef.index + 1 at hIndex
      change 0 < upper.2.val
      omega
    have hLow : (1 : Row) ≤ parentUpper.row := by
      simpa only [Frame.height, hCellEq] using
        Frame.one_le_height (build_normal_of_success hBuild).toOrdered hReal
    exact (le_of_not_gt hAbove).trans hLow

/-- A real executed copy requested at its source row has the bound in both
endpoint branches. Only the fixed branch needs the canonical source law. -/
theorem DynamicBlockState.copyEdge_source_row_father_bound
    {front : List Nat} {last : Nat} {p : Preparation front last}
    {block : Nat} {start ambient : Mountain} {references : List Ref} {next : Nat}
    (s : DynamicBlockState p block start references next ambient)
    {source : Ref} {sourceCell copied : Cell}
    (hSource : Canonical.cellAt p.reduced source = .ok sourceCell)
    (hRun : copyEdge ambient source (block * (p.reduced.size - 1 - p.root.column))
      p.root.column sourceCell.row = .ok copied) : CellRawFatherBound ambient copied := by
  intro ref parentUpper hLeft hParentUpper
  obtain ⟨actualSource, oldParent, hActualSource, _, hSourceLeft, _, hCases⟩ :=
    copyEdge_parent_cases hRun hLeft
  have hRead : lookup ambient source = .ok sourceCell := lookup_ok_iff.mpr
    (cellAt_ok_iff.mp (p.cell_read_preserved s.base_ambient hSource))
  have hEqual : actualSource = sourceCell := Except.ok.inj (hActualSource.symm.trans hRead)
  subst actualSource
  rw [copyEdge_return_row hRun]
  rcases hCases with ⟨hFixed, hRef⟩ | ⟨_, hBelow⟩
  · subst ref
    have hBefore : oldParent.column < p.reduced.size := by
      have := build_size p.reduced_build
      simp only [List.length_append, List.length_singleton] at this
      have := p.root_before_last
      omega
    have hParentRead : Canonical.cellAt p.reduced ⟨oldParent.column, oldParent.index + 1⟩ =
        .ok parentUpper :=
      (cellAt_eq_of_column_eq (ref := ⟨oldParent.column, oldParent.index + 1⟩)
        (s.base_ambient oldParent.column hBefore)).symm.trans hParentUpper
    exact build_stored_parent_upper_bound_all p.reduced_build hSource hSourceLeft hParentRead
  · exact below_parent_upper_bound_at hBelow hParentUpper

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.upper_of_refs
#print axioms OmegaY.Expansion.build_stored_parent_upper_bound
#print axioms OmegaY.Expansion.DynamicBlockState.fixed_source_parent_upper_bound
#print axioms OmegaY.Expansion.build_stored_parent_upper_bound_all
#print axioms OmegaY.Expansion.DynamicBlockState.copyEdge_source_row_father_bound
