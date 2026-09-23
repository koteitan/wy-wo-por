/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DecrementLowerKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.DecrementGraftKeys
import OmegaY.Expansion.InitialControlKeys

/-! Inverse provenance and exact keys of all actual reduced last-column
edges strictly below the old terminal top. These are precisely retained
lower edges of the actual initial control column. -/

namespace OmegaY.Expansion
open Canonical Geometry Frame

private theorem row_le_of_index {F : Frame} (hF : F.Ordered)
    {a b : F.Node} (hColumn : a.1 = b.1) (hIndex : a.2.val ≤ b.2.val) :
    F.height a ≤ F.height b := by
  cases a with
  | mk column index =>
    dsimp only at hColumn
    subst column
    exact (hF.rows_strict b.1).monotone hIndex

private theorem upper_exists_of_later {F : Frame} {node later : F.Node}
    (hColumn : node.1 = later.1) (hIndex : node.2.val < later.2.val) :
    ∃ upper, F.upper node = some upper := by
  cases node with
  | mk column index =>
    dsimp only at hColumn
    subst column
    change index.val < later.2.val at hIndex
    have hBound : index.val + 1 < F.length later.1 := by have := later.2.isLt; omega
    exact ⟨⟨later.1, ⟨index.val + 1, hBound⟩⟩, by simp only [Frame.upper, hBound, ↓reduceDIte]⟩

theorem Preparation.reduced_lower_edge_key
    {front : List Nat} {last : Nat} (p : Preparation front last)
    (g : RootGeometry p) (hLast : 1 < last)
    (edge : RealStoredEdge (Frame.ofMountain p.reduced))
    (hColumn : edge.lower.1.val = front.length)
    (hLow : (Frame.ofMountain p.reduced).height edge.upper < p.lastTop.row) :
    ∃ oldEdge : g.LowerEdge,
      Frame.ref oldEdge.val.parent = Frame.ref edge.parent ∧
      edge.degree = oldEdge.val.degree ∧
      ∀ (D : Nat) (labels : Nat → Model.Label),
        Keys.eval (edge.keyTemplate p.reduced_valid.toOrdered D) (fun column => labels column.val) =
          Keys.eval (oldEdge.val.keyTemplate p.initial_valid.toOrdered D) (fun column => labels column.val) := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hOldNormal := build_normal_of_success p.initial_build
  obtain ⟨seam, hSeamRef, _, hSuffix⟩ := p.reduced_exact_root_suffix hLast g
  have hSeamColumn : seam.1.val = front.length :=
    (congrArg Ref.column hSeamRef).trans g.lower_column
  have hSeamIndex : seam.2.val = g.lower.2.val := congrArg Ref.index hSeamRef
  have hUpperColumn : edge.upper.1.val = front.length :=
    (congrArg Fin.val (upper_spec edge.upper_eq).1).trans hColumn
  have hUpperBefore : edge.upper.2.val ≤ seam.2.val := by
    by_contra hn
    have hAfter : seam.2.val < edge.upper.2.val := Nat.lt_of_not_ge hn
    obtain ⟨oldHigh, hOldColumn, hOldIndex, hOldCell, _⟩ :=
      upperSuffix_later_correspondence
        (Fin.ext (hUpperColumn.trans hSeamColumn.symm)) hAfter hSuffix.symm
    obtain ⟨rootUpper, hRootUpper⟩ := upper_exists_of_later hOldColumn.symm hOldIndex
    have hRootHigh : p.lastTop.row ≤ F.height rootUpper := by
      have h := father_upper_bound_nodes hOldNormal g.lower_parent g.lower_upper hRootUpper
      simpa only [Frame.height, g.top_cell] using h
    have hUpperSpec := upper_spec hRootUpper
    have hHighRow : F.height rootUpper ≤ F.height oldHigh :=
      row_le_of_index p.initial_valid.toOrdered (hUpperSpec.1.trans hOldColumn.symm) (by omega)
    have hCellRow : F.height oldHigh = G.height edge.upper := congrArg Cell.row hOldCell
    exact not_lt_of_ge (hRootHigh.trans (hHighRow.trans_eq hCellRow)) hLow
  have hUpperIndex : edge.upper.2.val ≤ g.lower.2.val := by omega
  have hNewAdj := (upper_spec edge.upper_eq).2
  have hLowerIndex : edge.lower.2.val < g.lower.2.val := by omega
  let oldUpper : F.Node := ⟨g.lower.1, ⟨edge.upper.2.val, by
    have hLength : g.lower.2.val < F.length g.lower.1 := g.lower.2.isLt
    omega⟩⟩
  let oldLower : F.Node := ⟨g.lower.1, ⟨edge.lower.2.val, by
    have hLength : g.lower.2.val < F.length g.lower.1 := g.lower.2.isLt
    omega⟩⟩
  have hOldUpper : F.upper oldLower = some oldUpper := by
    have hBound : oldLower.2.val + 1 < F.length oldLower.1 := by
      have := oldUpper.2.isLt
      change edge.upper.2.val < F.length g.lower.1 at this
      change edge.lower.2.val + 1 < F.length g.lower.1
      omega
    simp only [Frame.upper, hBound, ↓reduceDIte]
    congr 2
    exact Fin.ext hNewAdj.symm
  have hOldReal : Real oldLower := edge.lower_real
  have hOldUpperLow : F.height oldUpper < p.lastTop.row :=
    (row_le_of_index p.initial_valid.toOrdered (a := oldUpper) (b := g.lower) rfl hUpperIndex).trans_lt g.lower_lt_top
  have hOldLowerLow : F.height oldLower < p.lastTop.row :=
    (row_le_of_index p.initial_valid.toOrdered (a := oldLower) (b := g.lower) rfl hLowerIndex.le).trans_lt g.lower_lt_top
  have hUpperRef : Frame.ref oldUpper = Frame.ref edge.upper := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨g.lower_column.trans hUpperColumn.symm, rfl⟩
  have hLowerRef : Frame.ref oldLower = Frame.ref edge.lower := by
    simp only [Frame.ref, Ref.mk.injEq]
    exact ⟨g.lower_column.trans hColumn.symm, rfl⟩
  have hUpperCell : G.cell edge.upper = decCell (F.cell oldUpper) := by
    have h := p.reduced_below_top_cell hLast oldUpper g.lower_column hOldUpperLow
    rw [hUpperRef] at h
    exact Except.ok.inj ((Canonical.cellAt_of_frame_node p.reduced edge.upper).symm.trans h)
  have hLowerCell : G.cell edge.lower = decCell (F.cell oldLower) := by
    have h := p.reduced_below_top_cell hLast oldLower g.lower_column hOldLowerLow
    rw [hLowerRef] at h
    exact Except.ok.inj ((Canonical.cellAt_of_frame_node p.reduced edge.lower).symm.trans h)
  obtain ⟨oldParent, hOldParent, _, _, hOldLeft⟩ :=
    hOldNormal.upper_step oldLower oldUpper hOldReal hOldUpper
  have hNewLeft : (G.cell edge.upper).left = some (Frame.ref edge.parent) := by
    obtain ⟨actualUpper, hActualUpper, hLeft⟩ := rawParent_spec edge.parent_eq
    have he : actualUpper = edge.upper := Option.some.inj (hActualUpper.symm.trans edge.upper_eq)
    exact he ▸ hLeft
  have hParentRef : Frame.ref oldParent = Frame.ref edge.parent := by
    have hLeft : (G.cell edge.upper).left = (F.cell oldUpper).left :=
      by simpa only [decCell] using congrArg Cell.left hUpperCell
    exact Option.some.inj (hOldLeft.symm.trans (hLeft.symm.trans hNewLeft))
  let oldEdge : RealStoredEdge F := {
    lower := oldLower, upper := oldUpper, parent := oldParent,
    lower_real := hOldReal, upper_eq := hOldUpper,
    parent_eq := (hOldNormal.rawParent_eq_P hOldReal).trans hOldParent }
  let oldPreserved := PreservesColumns.pop_prefix p.initial
  let newPreserved := p.initial_pop_preserved_reduced
  have hPrefixBound : oldParent.1.val < p.initial.pop.size := by
    rw [p.initial_pop_size]
    exact (P_column_lt hOldNormal.toOrdered hOldParent).trans_eq g.lower_column
  have hPrefixRead : Canonical.cellAt p.initial.pop (Frame.ref oldParent) = .ok (F.cell oldParent) :=
    (oldPreserved.cellAt hPrefixBound).symm.trans (Canonical.cellAt_of_frame_node p.initial oldParent)
  obtain ⟨commonParent, hCommonRef, _⟩ := Canonical.frame_node_of_cellAt hPrefixRead
  have hOldIdentity : oldEdge.parent = oldPreserved.mapNode commonParent :=
    Executable.ref_injective F (hCommonRef.symm.trans (oldPreserved.mapNode_ref commonParent).symm)
  have hNewIdentity : edge.parent = newPreserved.mapNode commonParent :=
    Executable.ref_injective G (hParentRef.symm.trans
      (hCommonRef.symm.trans (newPreserved.mapNode_ref commonParent).symm))
  have hRow : G.height edge.lower = F.height oldEdge.lower := by
    change (G.cell edge.lower).row = (F.cell oldLower).row
    exact (congrArg Cell.row hLowerCell).trans (decCell_row _)
  have hDegree := (storedEdge_key_eval_of_common_parent oldPreserved newPreserved
    p.initial_valid.pop.toOrdered p.initial_valid.toOrdered p.reduced_valid.toOrdered
    oldEdge edge commonParent hOldIdentity hNewIdentity hRow 0 (fun _ => (0 : Nat))).1
  refine ⟨⟨oldEdge, g.lower_column, hLowerIndex⟩, hParentRef, hDegree, ?_⟩
  intro D labels
  exact (storedEdge_key_eval_of_common_parent oldPreserved newPreserved
    p.initial_valid.pop.toOrdered p.initial_valid.toOrdered p.reduced_valid.toOrdered
    oldEdge edge commonParent hOldIdentity hNewIdentity hRow D labels).2

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.reduced_lower_edge_key
