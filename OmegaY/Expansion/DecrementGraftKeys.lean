/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DecrementGraftKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Geometry.RepresentedMountain
import OmegaY.Expansion.ActualHighRootFrontier
import OmegaY.Expansion.CommonPrefixKeys

/-!
# Exact edge keys in the genuine decrement graft

The suffix above the decrement seam is the old root's complete upper
suffix. Every actual edge there therefore has the same two cells and
the same parent reference as a real edge in the old root column. All
scale roots of that parent lie in the common complete prefix, so its
finite key evaluates identically under labels of original column indices.
The decrement seam itself and retained lower edges are not classified here.
-/

namespace OmegaY.Expansion
open Canonical Geometry Frame

private theorem index_lt_of_height {F : Frame} (hF : F.Ordered)
    {lower upper : F.Node} (hColumn : lower.1 = upper.1)
    (hHeight : F.height lower < F.height upper) : lower.2.val < upper.2.val := by
  cases lower with
  | mk column index =>
    dsimp only at hColumn
    subst column
    by_contra hn
    have hIndex : upper.2 ≤ index := Nat.le_of_not_gt hn
    exact not_lt_of_ge ((hF.rows_strict upper.1).monotone hIndex) hHeight

/-- The source prefix ending just before the old last column is genuinely
complete in both independently executed canonical builds. -/
theorem Preparation.initial_pop_preserved_reduced
    {front : List Nat} {last : Nat} (p : Preparation front last) :
    PreservesColumns p.initial.pop p.reduced := by
  have hSize := build_size p.initial_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hOld := PreservesColumns.pop_prefix p.initial
  intro column hColumn
  have hBefore : column < front.length := by
    simp only [Array.size_pop, hSize] at hColumn
    omega
  exact (build_changed_last_preserves_prefix p.initial_build p.reduced_build hBefore).symm.trans
    (hOld column hColumn)

/-- This is an inverse provenance statement for an actual high reduced
edge. Its old root-column edge, complete cells, parent reference and exact
key equality are conclusions, not chosen correspondence premises. -/
theorem Preparation.reduced_high_edge_key
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    (edge : RealStoredEdge (Frame.ofMountain p.reduced))
    (hColumn : edge.lower.1.val = front.length)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height edge.lower) :
    ∃ oldEdge : RealStoredEdge (Frame.ofMountain p.initial),
      oldEdge.lower.1.val = p.root.column ∧ p.root.index < oldEdge.lower.2.val ∧
      (Frame.ofMountain p.initial).cell oldEdge.lower = (Frame.ofMountain p.reduced).cell edge.lower ∧
      (Frame.ofMountain p.initial).cell oldEdge.upper = (Frame.ofMountain p.reduced).cell edge.upper ∧
      Frame.ref oldEdge.parent = Frame.ref edge.parent ∧
      edge.degree = oldEdge.degree ∧
      ∀ (D : Nat) (labels : Nat → Model.Label),
        Keys.eval (edge.keyTemplate p.reduced_valid.toOrdered D) (fun column => labels column.val) =
          Keys.eval (oldEdge.keyTemplate p.initial_valid.toOrdered D) (fun column => labels column.val) := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hOldNormal := build_normal_of_success p.initial_build
  obtain ⟨g⟩ := p.root_geometry hLast
  obtain ⟨seam, hSeamRef, hSeamCell, hSuffix⟩ := p.reduced_exact_root_suffix hLast g
  have hSeamColumn : seam.1.val = front.length :=
    (congrArg Ref.column hSeamRef).trans g.lower_column
  have hSeamRow : G.height seam = F.height g.lower := by
    simpa only [Frame.height, decCell_row] using congrArg Cell.row hSeamCell
  have hSameColumn : edge.lower.1 = seam.1 := Fin.ext (hColumn.trans hSeamColumn.symm)
  have hAbove : seam.2.val < edge.lower.2.val := by
    have hHeight : G.height seam < G.height edge.lower :=
      hSeamRow.trans_lt (g.lower_lt_top.trans_le hHigh)
    exact index_lt_of_height p.reduced_valid.toOrdered hSameColumn.symm hHeight
  obtain ⟨oldLower, hOldColumn, hOldIndex, hLowerCell, hLowerSuffix⟩ :=
    upperSuffix_later_correspondence hSameColumn hAbove hSuffix.symm
  obtain ⟨oldUpper, hOldUpper, hUpperCell⟩ :=
    (upperSuffix_upper_correspondence hLowerSuffix).1 edge.upper edge.upper_eq
  have hOldReal : Real oldLower := g.root_real.trans hOldIndex
  obtain ⟨oldParent, hOldParent, _, _, hOldLeft⟩ :=
    hOldNormal.upper_step oldLower oldUpper hOldReal hOldUpper
  have hOldRootColumn : oldLower.1.val = p.root.column :=
    (congrArg Fin.val hOldColumn).trans (congrArg Ref.column g.root_ref)
  have hParentGood : oldParent.1.val < p.root.column :=
    (P_column_lt hOldNormal.toOrdered hOldParent).trans_eq hOldRootColumn
  have hNewLeft : (G.cell edge.upper).left = some (Frame.ref edge.parent) := by
    obtain ⟨actualUpper, hActualUpper, hLeft⟩ := rawParent_spec edge.parent_eq
    have he : actualUpper = edge.upper := Option.some.inj (hActualUpper.symm.trans edge.upper_eq)
    exact he ▸ hLeft
  have hParentRef : Frame.ref oldParent = Frame.ref edge.parent :=
    Option.some.inj (hOldLeft.symm.trans ((congrArg Cell.left hUpperCell).trans hNewLeft))
  let oldEdge : RealStoredEdge F := {
    lower := oldLower, upper := oldUpper, parent := oldParent,
    lower_real := hOldReal, upper_eq := hOldUpper,
    parent_eq := (hOldNormal.rawParent_eq_P hOldReal).trans hOldParent }
  let oldPreserved := PreservesColumns.pop_prefix p.initial
  let newPreserved := p.initial_pop_preserved_reduced
  have hPrefixBound : oldParent.1.val < p.initial.pop.size := by
    have hSize := build_size p.initial_build
    simp only [List.length_append, List.length_singleton] at hSize
    simp only [Array.size_pop, hSize]
    have hBefore := hParentGood.trans p.root_before_last
    omega
  have hPrefixRead : Canonical.cellAt p.initial.pop (Frame.ref oldParent) = .ok (F.cell oldParent) :=
    (oldPreserved.cellAt hPrefixBound).symm.trans (Canonical.cellAt_of_frame_node p.initial oldParent)
  obtain ⟨commonParent, hCommonRef, _⟩ := Canonical.frame_node_of_cellAt hPrefixRead
  have hOldIdentity : oldEdge.parent = oldPreserved.mapNode commonParent :=
    Executable.ref_injective F (hCommonRef.symm.trans (oldPreserved.mapNode_ref commonParent).symm)
  have hNewIdentity : edge.parent = newPreserved.mapNode commonParent :=
    Executable.ref_injective G (hParentRef.symm.trans
      (hCommonRef.symm.trans (newPreserved.mapNode_ref commonParent).symm))
  have hRow : G.height edge.lower = F.height oldEdge.lower :=
    (congrArg Cell.row hLowerCell).symm
  have hDegree := (storedEdge_key_eval_of_common_parent oldPreserved newPreserved
    p.initial_valid.pop.toOrdered p.initial_valid.toOrdered p.reduced_valid.toOrdered
    oldEdge edge commonParent hOldIdentity hNewIdentity hRow 0 (fun _ => (0 : Nat))).1
  refine ⟨oldEdge, hOldRootColumn, ?_, hLowerCell, hUpperCell, hParentRef,
    hDegree, ?_⟩
  · have hRootIndex : g.rootNode.2.val = p.root.index := congrArg Ref.index g.root_ref
    change p.root.index < oldLower.2.val
    omega
  · intro D labels
    exact (storedEdge_key_eval_of_common_parent oldPreserved newPreserved
      p.initial_valid.pop.toOrdered p.initial_valid.toOrdered p.reduced_valid.toOrdered
      oldEdge edge commonParent hOldIdentity hNewIdentity hRow D labels).2

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.initial_pop_preserved_reduced
#print axioms OmegaY.Expansion.Preparation.reduced_high_edge_key
