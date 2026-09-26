/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/DecrementSeamKeys.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.DecrementGraftKeys
import OmegaY.Expansion.CommonPrefixDegreeKeys

/-!
# The real first graft seam has the old root edge's exact key

The lower and upper rows straddle the original terminal-top row. Exact
decrement execution identifies this particular returned edge as the seam.
Its lower row may differ from the old root's row, but lies in the root
edge's half-open interval. Its actual parent and degree, and therefore
every finite key coordinate, agree with the old root edge.
-/

namespace OmegaY.Row

theorem jump_eq_of_between_B {a b c : Row} (hba : b ≤ a) (hcb : c ≤ b)
    (ha : a < B b c) : jump a c = jump b c := by
  have hInside : jump b a ≤ jump b c := jump_le_of_lt_bump hba ha
  calc
    jump a c = jump c a := jump_comm _ _
    _ = max (jump c b) (jump b a) := jump_max hcb hba
    _ = jump b c := by rw [jump_comm c b, max_eq_left hInside]

end OmegaY.Row

namespace OmegaY.Expansion
open Canonical Geometry Frame

private theorem index_lt_of_row {F : Frame} (hF : F.Ordered)
    {lower upper : F.Node} (hColumn : lower.1 = upper.1)
    (hHeight : F.height lower < F.height upper) : lower.2.val < upper.2.val := by
  cases lower with
  | mk column index =>
    dsimp only at hColumn
    subst column
    by_contra hn
    have hIndex : upper.2 ≤ index := Nat.le_of_not_gt hn
    exact not_lt_of_ge ((hF.rows_strict upper.1).monotone hIndex) hHeight

private theorem upper_exists_of_later {F : Frame} {node later : F.Node}
    (hColumn : node.1 = later.1) (hIndex : node.2.val < later.2.val) :
    ∃ upper, F.upper node = some upper := by
  rcases node with ⟨column, index⟩
  dsimp only at hColumn
  subst column
  change index.val < later.2.val at hIndex
  have hBound : index.val + 1 < F.length later.1 := by have := later.2.isLt; omega
  exact ⟨⟨later.1, ⟨index.val + 1, hBound⟩⟩, by simp only [Frame.upper, hBound, ↓reduceDIte]⟩

private theorem lower_eq_of_straddling {F : Frame} (hF : F.Ordered)
    {left leftUpper right rightUpper : F.Node}
    (hReal : Real left) (hLeft : F.upper left = some leftUpper)
    (hRight : F.upper right = some rightUpper) (hColumn : left.1 = right.1)
    {cut : Row} (hLeftLow : F.height left < cut) (hLeftHigh : cut ≤ F.height leftUpper)
    (hRightLow : F.height right < cut) (hRightHigh : cut ≤ F.height rightUpper) :
    left = right := by
  let inside := max (F.height left) (F.height right)
  have hInside : (1 : Row) ≤ inside := (one_le_height hF hReal).trans (le_max_left _ _)
  have hBelow : inside < cut := max_lt hLeftLow hRightLow
  have hLeftFront : frontierAt hF inside hInside left.1 = left := by
    apply frontierAt_eq_of_upper_barrier hF hInside (le_max_left _ _)
    intro upper hUpper
    have he : upper = leftUpper := Option.some.inj (hUpper.symm.trans hLeft)
    exact hBelow.trans_le (hLeftHigh.trans_eq (congrArg F.height he).symm)
  have hRightFront : frontierAt hF inside hInside right.1 = right := by
    apply frontierAt_eq_of_upper_barrier hF hInside (le_max_right _ _)
    intro upper hUpper
    have he : upper = rightUpper := Option.some.inj (hUpper.symm.trans hRight)
    exact hBelow.trans_le (hRightHigh.trans_eq (congrArg F.height he).symm)
  exact hLeftFront.symm.trans ((congrArg (frontierAt hF inside hInside) hColumn).trans hRightFront)

/-- No source seam edge is supplied: an actual returned edge straddling
Z forces the old root to have an upper, and constructs that exact edge. -/
theorem Preparation.reduced_seam_edge_key
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    (edge : RealStoredEdge (Frame.ofMountain p.reduced))
    (hColumn : edge.lower.1.val = front.length)
    (hLow : (Frame.ofMountain p.reduced).height edge.lower < p.lastTop.row)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).height edge.upper) :
    ∃ oldEdge : RealStoredEdge (Frame.ofMountain p.initial),
      Frame.ref oldEdge.lower = p.root ∧
      (Frame.ofMountain p.reduced).cell edge.upper = (Frame.ofMountain p.initial).cell oldEdge.upper ∧
      Frame.ref edge.parent = Frame.ref oldEdge.parent ∧
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
  have hSeamLow : G.height seam < p.lastTop.row := hSeamRow.trans_lt g.lower_lt_top
  have hSameColumn : edge.lower.1 = seam.1 := Fin.ext (hColumn.trans hSeamColumn.symm)
  have hUpperColumn : edge.upper.1 = seam.1 := (upper_spec edge.upper_eq).1.trans hSameColumn
  have hAfter : seam.2.val < edge.upper.2.val :=
    index_lt_of_row p.reduced_valid.toOrdered hUpperColumn.symm (hSeamLow.trans_le hHigh)
  obtain ⟨oldHigh, hOldHighColumn, hOldHighIndex, _, _⟩ :=
    upperSuffix_later_correspondence hUpperColumn hAfter hSuffix.symm
  obtain ⟨rootUpper, hRootUpper⟩ := upper_exists_of_later hOldHighColumn.symm hOldHighIndex
  obtain ⟨parent, hParent, hRootRow, _, hRootLeft⟩ :=
    hOldNormal.upper_step g.rootNode rootUpper g.root_real hRootUpper
  obtain ⟨seamUpper, hSeamUpper, hSeamUpperCell⟩ :=
    (upperSuffix_upper_correspondence hSuffix).1 rootUpper hRootUpper
  have hRootHigh : p.lastTop.row ≤ F.height rootUpper := by
    have hD := father_upper_bound_nodes hOldNormal g.lower_parent g.lower_upper hRootUpper
    simpa only [Frame.height, g.top_cell] using hD
  have hSeamHigh : p.lastTop.row ≤ G.height seamUpper :=
    hRootHigh.trans_eq (congrArg Cell.row hSeamUpperCell).symm
  have hSeamEq : edge.lower = seam := lower_eq_of_straddling p.reduced_valid.toOrdered
    edge.lower_real edge.upper_eq hSeamUpper hSameColumn hLow hHigh hSeamLow hSeamHigh
  have hUpperEq : edge.upper = seamUpper :=
    Option.some.inj (edge.upper_eq.symm.trans (by simpa only [hSeamEq] using hSeamUpper))
  have hUpperCell : G.cell edge.upper = F.cell rootUpper :=
    (congrArg G.cell hUpperEq).trans hSeamUpperCell
  have hLowerRow : G.height edge.lower = F.height g.lower :=
    (congrArg G.height hSeamEq).trans hSeamRow
  have hNewLeft : (G.cell edge.upper).left = some (Frame.ref edge.parent) := by
    obtain ⟨actualUpper, hActualUpper, hLeft⟩ := rawParent_spec edge.parent_eq
    have he : actualUpper = edge.upper := Option.some.inj (hActualUpper.symm.trans edge.upper_eq)
    exact he ▸ hLeft
  have hParentRef : Frame.ref edge.parent = Frame.ref parent :=
    Option.some.inj (hNewLeft.symm.trans ((congrArg Cell.left hUpperCell).trans hRootLeft))
  let oldEdge : RealStoredEdge F := {
    lower := g.rootNode, upper := rootUpper, parent := parent,
    lower_real := g.root_real, upper_eq := hRootUpper,
    parent_eq := (hOldNormal.rawParent_eq_P g.root_real).trans hParent }
  let oldPreserved := PreservesColumns.pop_prefix p.initial
  let newPreserved := p.initial_pop_preserved_reduced
  have hParentGood : parent.1.val < p.root.column :=
    (P_column_lt hOldNormal.toOrdered hParent).trans_eq (congrArg Ref.column g.root_ref)
  have hPrefixBound : parent.1.val < p.initial.pop.size := by
    have hSize := build_size p.initial_build
    simp only [List.length_append, List.length_singleton] at hSize
    simp only [Array.size_pop, hSize]
    have hBefore := hParentGood.trans p.root_before_last
    omega
  have hCommonRead : Canonical.cellAt p.initial.pop (Frame.ref parent) = .ok (F.cell parent) :=
    (oldPreserved.cellAt hPrefixBound).symm.trans (Canonical.cellAt_of_frame_node p.initial parent)
  obtain ⟨commonParent, hCommonRef, _⟩ := Canonical.frame_node_of_cellAt hCommonRead
  have hOldIdentity : oldEdge.parent = oldPreserved.mapNode commonParent :=
    Executable.ref_injective F (hCommonRef.symm.trans (oldPreserved.mapNode_ref commonParent).symm)
  have hNewIdentity : edge.parent = newPreserved.mapNode commonParent :=
    Executable.ref_injective G (hParentRef.trans
      (hCommonRef.symm.trans (newPreserved.mapNode_ref commonParent).symm))
  have hParentRow : G.height edge.parent = F.height parent := by
    rw [hNewIdentity, newPreserved.mapNode_height]
    have hOldHeight := oldPreserved.mapNode_height commonParent
    rw [← hOldIdentity] at hOldHeight
    exact hOldHeight.symm
  have hDegree : edge.degree = oldEdge.degree := by
    change Row.jump (G.height edge.lower) (G.height edge.parent) =
      Row.jump (F.height g.rootNode) (F.height parent)
    rw [hLowerRow, hParentRow]
    apply Row.jump_eq_of_between_B (P_height_le hOldNormal.toOrdered g.lower_parent)
      (P_height_le hOldNormal.toOrdered hParent)
    exact g.lower_lt_top.trans_le (hRootHigh.trans_eq hRootRow)
  refine ⟨oldEdge, g.root_ref, hUpperCell, hParentRef, hDegree, ?_⟩
  intro D labels
  exact storedEdge_key_eval_of_common_parent_degree oldPreserved newPreserved
    p.initial_valid.pop.toOrdered p.initial_valid.toOrdered p.reduced_valid.toOrdered
    oldEdge edge commonParent hOldIdentity hNewIdentity hDegree D labels

end OmegaY.Expansion

#print axioms OmegaY.Row.jump_eq_of_between_B
#print axioms OmegaY.Expansion.Preparation.reduced_seam_edge_key
