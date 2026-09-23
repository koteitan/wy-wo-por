/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/LowBoundaryRecordPath.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CanonicalCutProjection
import OmegaY.Expansion.BoundaryRecordPath
import OmegaY.Expansion.RawFatherBound

/-! Initial references for real root-prefix nodes strictly below the bad
root reach the original root node by actual stored-parent edges. The first
edge is retained by exact decrement; all later edges use unchanged complete
columns. No boundary path or copied normality is an input. -/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem low_upper_ref {F : Frame} {u upper : F.Node}
    (hUpper : F.upper u = some upper) :
    Frame.ref upper = ⟨u.1.val, u.2.val + 1⟩ := by
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨congrArg Fin.val (Frame.upper_spec hUpper).1, (Frame.upper_spec hUpper).2⟩

private theorem low_height_le_of_index {F : Frame} (hF : F.Ordered) {u v : F.Node}
    (hColumn : u.1 = v.1) (hIndex : u.2.val ≤ v.2.val) : F.height u ≤ F.height v := by
  rcases u with ⟨c, i⟩
  dsimp only at hColumn
  subst c
  exact (hF.rows_strict v.1).monotone hIndex

private theorem low_index_lt_of_height {F : Frame} (hF : F.Ordered) {u v : F.Node}
    (hColumn : u.1 = v.1) (hHeight : F.height u < F.height v) : u.2.val < v.2.val := by
  by_contra hn
  exact (not_lt_of_ge (low_height_le_of_index hF hColumn.symm (Nat.le_of_not_gt hn))) hHeight

/-- An entire old parent path to the left of the changed last column is
retained as actual array edges, including upper-neighbor references. -/
theorem Preparation.initial_parent_path_left {front : List Nat} {last : Nat}
    (p : Preparation front last) {u v : (Frame.ofMountain p.initial).Node}
    (hPath : Frame.ParentPath (Frame.ofMountain p.initial) u v)
    (hLeft : u.1.val < front.length) :
    RawRefPath p.reduced (Frame.ref u) (Frame.ref v) := by
  have hNormal := build_normal_of_success p.initial_build
  induction hPath with
  | refl _ => exact .refl _
  | @cons u q v hParent rest ih =>
    have hReal : Frame.Real u := Frame.real_of_value_pos hNormal.toOrdered
      ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
    have hRaw := (hNormal.rawParent_eq_P hReal).trans hParent
    have hEdge := RawRefEdge.of_rawParent hRaw
    obtain ⟨lower, upper, parentCell, hLower, hUpper, hStored, hRead⟩ := hEdge
    have hParentLeft := (Frame.P_column_lt hNormal.toOrdered hParent).trans hLeft
    apply RawRefPath.cons
      (next := Frame.ref q)
      (show RawRefEdge p.reduced (Frame.ref u) (Frame.ref q) from
        ⟨lower, upper, parentCell,
          (build_changed_last_preserves_ref p.initial_build p.reduced_build hLeft).symm.trans hLower,
          (build_changed_last_preserves_ref (ref := ⟨u.1.val, u.2.val + 1⟩)
            p.initial_build p.reduced_build hLeft).symm.trans hUpper,
          hStored,
          (build_changed_last_preserves_ref p.initial_build p.reduced_build hParentLeft).symm.trans hRead⟩)
    exact ih hParentLeft

/-- A projected initial path starts below a cap at or below the old
penultimate node. Both cells of its first edge therefore survive decrement
at their original indices. The selector itself is preserved as a conclusion. -/
theorem Preparation.decrement_projected_path {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) (g : RootGeometry p)
    {reference root : (Frame.ofMountain p.initial).Node} {cap : Row}
    (hColumn : reference.1.val = front.length) (hRootLeft : root.1.val < front.length)
    (hBelow : below p.initial front.length cap = .ok (Frame.ref reference))
    (hLow : (Frame.ofMountain p.initial).height reference < cap)
    (hCap : cap ≤ (Frame.ofMountain p.initial).height g.lower)
    (hPath : Frame.ParentPath (Frame.ofMountain p.initial) reference root) :
    below p.reduced (p.reduced.size - 1) cap = .ok (Frame.ref reference) ∧
      Canonical.cellAt p.reduced (Frame.ref reference) =
        .ok (decCell ((Frame.ofMountain p.initial).cell reference)) ∧
      RawRefPath p.reduced (Frame.ref reference) (Frame.ref root) := by
  let F := Frame.ofMountain p.initial
  have hNormal : F.Normal := build_normal_of_success p.initial_build
  cases hPath with
  | refl => omega
  | @cons reference q root hParent rest =>
    obtain ⟨upper, hUpper⟩ := hNormal.upper_of_parent hParent
    have hUpperRef := low_upper_ref hUpper
    have hSame : reference.1 = g.lower.1 := Fin.ext (hColumn.trans g.lower_column.symm)
    have hReferenceIndex := low_index_lt_of_height hNormal.toOrdered hSame (hLow.trans_le hCap)
    have hUpperIndex : upper.2.val ≤ g.lower.2.val := by
      have := (Frame.upper_spec hUpper).2
      omega
    have hUpperHeight : F.height upper ≤ F.height g.lower :=
      low_height_le_of_index hNormal.toOrdered ((Frame.upper_spec hUpper).1.trans hSame) hUpperIndex
    have hUpperColumn : upper.1.val = front.length :=
      (congrArg Fin.val (Frame.upper_spec hUpper).1).trans hColumn
    have hLowerRead := p.reduced_below_top_cell hLast reference hColumn
      ((hLow.trans_le hCap).trans g.lower_lt_top)
    have hUpperRead := p.reduced_below_top_cell hLast upper hUpperColumn
      (hUpperHeight.trans_lt g.lower_lt_top)
    have hOldUpper : Canonical.cellAt p.initial
        ⟨(Frame.ref reference).column, (Frame.ref reference).index + 1⟩ = .ok (F.cell upper) := by
      change Canonical.cellAt p.initial ⟨reference.1.val, reference.2.val + 1⟩ = _
      rw [← hUpperRef]
      exact Canonical.cellAt_of_frame_node p.initial upper
    have hUpperCap : cap ≤ F.height upper := below_parent_upper_bound_at hBelow hOldUpper
    have hReadUpper : Canonical.cellAt p.reduced
        ⟨reference.1.val, reference.2.val + 1⟩ = .ok (decCell (F.cell upper)) := by
      rw [← hUpperRef]
      exact hUpperRead
    obtain ⟨nodes, hNodes, hLowerIndex⟩ := cellAt_ok_iff.mp hLowerRead
    obtain ⟨upperNodes, hUpperNodes, hUpperAt⟩ := cellAt_ok_iff.mp hReadUpper
    have hNodesEq : upperNodes = nodes := Option.some.inj (hUpperNodes.symm.trans hNodes)
    subst upperNodes
    have hSelect := below_eq_of_adjacent p.reduced_valid hNodes hLowerIndex hUpperAt
      (show (decCell (F.cell reference)).row < cap from hLow)
      (show cap ≤ (decCell (F.cell upper)).row from hUpperCap)
    have hSize := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hSize
    have hLastColumn : reference.1.val = p.reduced.size - 1 := by omega
    have hReal : Frame.Real reference := Frame.real_of_value_pos hNormal.toOrdered
      ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
    obtain ⟨actualParent, hActualParent, _, _, hStored⟩ :=
      hNormal.upper_step reference upper hReal hUpper
    have hParentEq : actualParent = q := Option.some.inj (hActualParent.symm.trans hParent)
    subst actualParent
    have hParentLeft : q.1.val < front.length := by
      simpa only [hColumn] using Frame.P_column_lt hNormal.toOrdered hParent
    have hParentRead : Canonical.cellAt p.reduced (Frame.ref q) = .ok (F.cell q) :=
      (build_changed_last_preserves_ref p.initial_build p.reduced_build hParentLeft).symm.trans
        (Canonical.cellAt_of_frame_node p.initial q)
    refine ⟨?_, hLowerRead, RawRefPath.cons ?_ (p.initial_parent_path_left rest hParentLeft)⟩
    · change below p.reduced (Frame.ref reference).column cap = .ok (Frame.ref reference) at hSelect
      simpa only [Frame.ref, hLastColumn] using hSelect
    · exact ⟨_, _, _, hLowerRead, hReadUpper, hStored, hParentRead⟩

/-- Every real lower root interval has the paper's initial path
`reference →* original root`. The reference is the actual reduced selector;
the root and cap are actual consecutive nodes of the original root column. -/
theorem Preparation.initial_low_root_reference_path {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper) :
    ∃ (reference : Ref) (cell : Cell),
      below p.reduced (p.reduced.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
        .ok reference ∧
      Canonical.cellAt p.reduced reference = .ok cell ∧
      (Frame.ofMountain p.initial).height root ≤ cell.row ∧
      cell.row < (Frame.ofMountain p.initial).height rootUpper ∧
      RawRefPath p.reduced reference (Frame.ref root) := by
  let F := Frame.ofMountain p.initial
  have hNormal : F.Normal := build_normal_of_success p.initial_build
  obtain ⟨g⟩ := p.root_geometry hLast
  have hSame : root.1 = g.rootNode.1 :=
    Fin.ext (hRootColumn.trans (congrArg Ref.column g.root_ref).symm)
  have hUpperIndex : rootUpper.2.val ≤ g.rootNode.2.val := by
    have hi := congrArg Ref.index g.root_ref
    have hu := (Frame.upper_spec hRootUpper).2
    change g.rootNode.2.val = p.root.index at hi
    omega
  have hCap : F.height rootUpper ≤ F.height g.rootNode :=
    low_height_le_of_index hNormal.toOrdered ((Frame.upper_spec hRootUpper).1.trans hSame) hUpperIndex
  obtain ⟨reference, _, hColumn, hBelow, hLow, hPath⟩ :=
    build_parent_path_below_parent_upper p.initial_build g.lower_parent hRootReal hSame hRootUpper hCap
  have hRefColumn : reference.1.val = front.length := (congrArg Fin.val hColumn).trans g.lower_column
  have hBelow' : below p.initial front.length (F.height rootUpper) = .ok (Frame.ref reference) := by
    simpa only [g.lower_column] using hBelow
  have hRootHeight : F.height g.rootNode = p.rootCell.row := congrArg Cell.row g.root_cell
  obtain ⟨hSelected, hRead, hReducedPath⟩ := p.decrement_projected_path hLast g hRefColumn
    (hRootColumn ▸ p.root_before_last) hBelow' hLow
    (hCap.trans (hRootHeight.trans_le g.root_le_lower)) hPath
  exact ⟨Frame.ref reference, decCell (F.cell reference), hSelected, hRead,
    hPath.height_le hNormal.toOrdered, hLow, hReducedPath⟩

/-- Determinism identifies any actual selector result with the constructed
path endpoint; no separate ancestry certificate is required from the caller. -/
theorem Preparation.initial_low_root_selected_path {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper)
    {reference : Ref}
    (hBelow : below p.reduced (p.reduced.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
      .ok reference) : RawRefPath p.reduced reference (Frame.ref root) := by
  obtain ⟨found, _, hFound, _, _, _, hPath⟩ :=
    p.initial_low_root_reference_path hLast hRootReal hRootColumn hBefore hRootUpper
  have he : found = reference := Except.ok.inj (hFound.symm.trans hBelow)
  exact he ▸ hPath

/-- The real reference map queries precisely the cap used above. Its
boundary position and exact successor cap are derived from preparation. -/
theorem Preparation.initial_low_root_reference_query_path {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper)
    {references : List Ref}
    (hMap : p.boundaries.mapM (below p.reduced (p.reduced.size - 1)) = .ok references) :
    ∃ (reference : Ref) (cell : Cell),
      below p.reduced (p.reduced.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
        .ok reference ∧
      Canonical.cellAt p.reduced reference = .ok cell ∧
      referenceAt p.reduced references ((Frame.ofMountain p.initial).height root) = .ok cell.row ∧
      (Frame.ofMountain p.initial).height root ≤ cell.row ∧
      cell.row < (Frame.ofMountain p.initial).height rootUpper ∧
      RawRefPath p.reduced reference (Frame.ref root) := by
  let F := Frame.ofMountain p.initial
  have hNodes : p.initial[p.root.column]? = some p.initial[root.1.val] := by
    rw [← hRootColumn]
    exact Array.getElem?_eq_getElem root.1.isLt
  have hRootRead : p.initial[root.1.val][root.2.val]? = some (F.cell root) :=
    Array.getElem?_eq_getElem root.2.isLt
  have hUpperRead : p.initial[root.1.val][root.2.val + 1]? = some (F.cell rootUpper) := by
    have hRef := low_upper_ref hRootUpper
    have hFull := Canonical.cellAt_of_frame_node p.initial rootUpper
    rw [hRef] at hFull
    obtain ⟨nodes, hColumn, hRead⟩ := cellAt_ok_iff.mp hFull
    have he : nodes = p.initial[root.1.val] := Option.some.inj
      (hColumn.symm.trans (Array.getElem?_eq_getElem root.1.isLt))
    exact he ▸ hRead
  obtain ⟨earlier, cap, later, degree, hPartition, hPower, _, hLater, hHigher⟩ :=
    p.root_boundary_partition hLast hNodes hRootRead hBefore.le
  have hCapEq : cap = F.height rootUpper :=
    p.boundary_cap_eq_next hLast hNodes hRootRead hUpperRead hBefore
      (by rw [hPartition]; simp) (by rw [hPower]; exact Row.lt_bump _ _)
      (hHigher (root.2.val + 1) (F.cell rootUpper) (by omega) (by omega) hUpperRead)
  rw [hCapEq] at hPartition
  obtain ⟨reference, cell, hBelow, hRead, hLower, hUpper, hPath⟩ :=
    p.initial_low_root_reference_path hLast hRootReal hRootColumn hBefore hRootUpper
  have hQuery := referenceAt_of_boundary_partition
    (Array.getElem?_eq_getElem p.reduced_last_exists) hPartition hMap hBelow
    (lookup_ok_iff.mpr (cellAt_ok_iff.mp hRead)) hLower hLater
  exact ⟨reference, cell, hBelow, hRead, hQuery, hLower, hUpper, hPath⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_parent_path_left
#print axioms OmegaY.Expansion.Preparation.decrement_projected_path
#print axioms OmegaY.Expansion.Preparation.initial_low_root_reference_path
#print axioms OmegaY.Expansion.Preparation.initial_low_root_selected_path
#print axioms OmegaY.Expansion.Preparation.initial_low_root_reference_query_path
