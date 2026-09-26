/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighRootFrontier.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualIteratedHighestBoundary
import OmegaY.Expansion.ActualLowEffectiveCandidate
import OmegaY.Expansion.FrontierEvents
import OmegaY.Expansion.ActualHighFrontierCopy

/-!
# Actual root-boundary frontiers above the original terminal top

The root suffix is identified from the executed decrement graft. Later
boundary frontiers are actual effective occurrences of those source nodes.
The fixed original parent is retained as a complete reference and cell;
no numerical parent recognition in a copied column is assumed.
-/

namespace OmegaY.Expansion

open Canonical Geometry

/-- Equality of complete strict upper suffixes identifies every later
source cell and its remaining suffix in the other actual column. -/
theorem upperSuffix_later_correspondence {before after : Mountain}
    {base source : (Frame.ofMountain before).Node}
    {target : (Frame.ofMountain after).Node}
    (hColumn : source.1 = base.1) (hAfter : base.2.val < source.2.val)
    (hSuffix : upperSuffix after target = upperSuffix before base) :
    ∃ next : (Frame.ofMountain after).Node,
      next.1 = target.1 ∧ target.2.val < next.2.val ∧
      (Frame.ofMountain after).cell next = (Frame.ofMountain before).cell source ∧
      upperSuffix after next = upperSuffix before source := by
  let offset := source.2.val - (base.2.val + 1)
  have hOffset : base.2.val + 1 + offset = source.2.val := by dsimp [offset]; omega
  have hSourceAt : before[base.1.val][source.2.val]? =
      some ((Frame.ofMountain before).cell source) := by
    change before[base.1.val][source.2.val]? = some before[source.1.val][source.2.val]
    simpa only [hColumn] using Array.getElem?_eq_getElem source.2.isLt
  have hAt : (upperSuffix after target)[offset]? =
      some ((Frame.ofMountain before).cell source) := by
    rw [hSuffix]
    simpa only [upperSuffix, List.getElem?_drop, hOffset, Array.getElem?_toList] using hSourceAt
  have hTargetAt : after[target.1.val][target.2.val + 1 + offset]? =
      some ((Frame.ofMountain before).cell source) := by
    simpa only [upperSuffix, List.getElem?_drop, Array.getElem?_toList] using hAt
  have hRead : Canonical.cellAt after ⟨target.1.val, target.2.val + 1 + offset⟩ =
      .ok ((Frame.ofMountain before).cell source) := cellAt_ok_iff.mpr
    ⟨after[target.1.val], Array.getElem?_eq_getElem target.1.isLt, hTargetAt⟩
  obtain ⟨next, hRef, hCell⟩ := Canonical.frame_node_of_cellAt hRead
  have hNextColumn : next.1 = target.1 := Fin.ext (congrArg Ref.column hRef)
  have hNextIndex : next.2.val = target.2.val + 1 + offset := congrArg Ref.index hRef
  refine ⟨next, hNextColumn, by omega, hCell, ?_⟩
  have hDrop := congrArg (fun cells : List Cell => cells.drop (offset + 1)) hSuffix
  simpa only [upperSuffix, List.drop_drop, hNextColumn, hColumn, hNextIndex,
    ← Nat.add_assoc, hOffset] using hDrop

/-- Identical strict upper suffixes preserve the next actual cell,
including all of its stored references, or preserve absence of an upper. -/
theorem upperSuffix_upper_correspondence {before after : Mountain}
    {source : (Frame.ofMountain before).Node} {target : (Frame.ofMountain after).Node}
    (hSuffix : upperSuffix after target = upperSuffix before source) :
    (∀ sourceUpper, (Frame.ofMountain before).upper source = some sourceUpper →
      ∃ targetUpper, (Frame.ofMountain after).upper target = some targetUpper ∧
        (Frame.ofMountain after).cell targetUpper = (Frame.ofMountain before).cell sourceUpper) ∧
    ((Frame.ofMountain before).upper source = none →
      (Frame.ofMountain after).upper target = none) := by
  constructor
  · intro sourceUpper hSourceUpper
    cases hTargetUpper : (Frame.ofMountain after).upper target with
    | none =>
        rw [upperSuffix_of_upper_none hTargetUpper, upperSuffix_of_upper hSourceUpper] at hSuffix
        cases hSuffix
    | some targetUpper =>
        rw [upperSuffix_of_upper hTargetUpper, upperSuffix_of_upper hSourceUpper] at hSuffix
        exact ⟨targetUpper, rfl, (List.cons.inj hSuffix).1⟩
  · intro hSourceUpper
    cases hTargetUpper : (Frame.ofMountain after).upper target with
    | none => rfl
    | some targetUpper =>
        rw [upperSuffix_of_upper hTargetUpper, upperSuffix_of_upper_none hSourceUpper] at hSuffix
        cases hSuffix

/-- Every original root-column node at or above the bad root has a
specific actual reduced last-column counterpart. At the bad root only
its height changes; above it the complete source cell is retained. -/
theorem Preparation.reduced_root_node_correspondence
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    (g : RootGeometry p) {rootSource : (Frame.ofMountain p.initial).Node}
    (hColumn : rootSource.1.val = p.root.column)
    (hAfter : p.root.index ≤ rootSource.2.val) :
    ∃ source : (Frame.ofMountain p.reduced).Node,
      source.1.val = p.reduced.size - 1 ∧ Frame.Real source ∧
      upperSuffix p.reduced source = upperSuffix p.initial rootSource ∧
      ((rootSource = g.rootNode ∧ (Frame.ofMountain p.reduced).height source < p.lastTop.row) ∨
        (Frame.ofMountain p.reduced).cell source = (Frame.ofMountain p.initial).cell rootSource) := by
  obtain ⟨lower, hRef, hCell, hSuffix⟩ := p.reduced_exact_root_suffix hLast g
  have hLowerColumn : lower.1.val = p.reduced.size - 1 := by
    have hc := congrArg Ref.column hRef
    have hs := build_size p.reduced_build
    simp only [List.length_append, List.length_singleton] at hs
    change lower.1.val = g.lower.1.val at hc
    rw [hc, g.lower_column]
    omega
  have hLowerReal : Frame.Real lower := by
    have hi : lower.2.val = g.lower.2.val := congrArg Ref.index hRef
    change 0 < lower.2.val
    rw [hi]
    exact g.lower_real
  have hSourceColumn : rootSource.1 = g.rootNode.1 :=
    Fin.ext (hColumn.trans (congrArg Ref.column g.root_ref).symm)
  have hRootIndex : g.rootNode.2.val = p.root.index := congrArg Ref.index g.root_ref
  by_cases he : rootSource.2.val = p.root.index
  · have hNodeEq : rootSource = g.rootNode := by
      apply Executable.ref_injective (Frame.ofMountain p.initial)
      exact congrArg₂ Ref.mk (congrArg Fin.val hSourceColumn) (he.trans hRootIndex.symm)
    refine ⟨lower, hLowerColumn, hLowerReal, by simpa only [hNodeEq] using hSuffix,
      Or.inl ⟨hNodeEq, ?_⟩⟩
    change ((Frame.ofMountain p.reduced).cell lower).row < _
    rw [hCell, decCell_row]
    exact g.lower_lt_top
  · obtain ⟨source, hSourceCol, hSourceIndex, hSourceCell, hSourceSuffix⟩ :=
      upperSuffix_later_correspondence hSourceColumn (by omega) hSuffix
    exact ⟨source, (congrArg Fin.val hSourceCol).trans hLowerColumn,
      hLowerReal.trans hSourceIndex, hSourceSuffix, Or.inr hSourceCell⟩

private theorem normal_upper_none_of_parent_none {F : Frame} (hNormal : F.Normal)
    {node : F.Node} (hReal : Frame.Real node) (hNone : F.P node = none) : F.upper node = none := by
  cases hUpper : F.upper node with
  | none => rfl
  | some upper =>
      obtain ⟨parent, hParent, _⟩ := hNormal.upper_step node upper hReal hUpper
      rw [hNone] at hParent
      cases hParent

private theorem normal_value_one_of_upper_none {F : Frame} (hNormal : F.Normal)
    {node : F.Node} (hReal : Frame.Real node) (hNone : F.upper node = none) : F.value node = 1 := by
  have hp := hNormal.real_positive node hReal
  by_contra hn
  obtain ⟨upper, hUpper⟩ := hNormal.upper_exists node hReal (by omega)
  rw [hNone] at hUpper
  cases hUpper

private theorem index_le_of_frontier {F : Frame} (hF : F.Ordered)
    {cut : Row} (hOne : (1 : Row) ≤ cut) {source other : F.Node}
    (hFrontier : Frame.frontierAt hF cut hOne source.1 = source)
    (hColumn : other.1 = source.1) (hBelow : F.height other ≤ cut) :
    other.2.val ≤ source.2.val := by
  rcases source with ⟨column, index⟩
  rcases other with ⟨otherColumn, otherIndex⟩
  dsimp only at hColumn
  subst otherColumn
  have hMax := (Frame.frontierAt_spec hF hOne column).2.2.2.1 otherIndex hBelow
  change Frame.frontierAt hF cut hOne column = ⟨column, index⟩ at hFrontier
  have hi := congrArg (fun node : F.Node => node.2.val) hFrontier
  change otherIndex.val ≤ (Frame.frontierAt hF cut hOne column).2.val at hMax
  exact hMax.trans_eq hi

/-- The source numerical father of any root-column node is fixed to
the left. The actual graft's equal upper cell therefore produces the
same numerical father in the independently built reduced mountain. -/
theorem Preparation.reduced_root_suffix_parent
    {front : List Nat} {last : Nat} (p : Preparation front last)
    {rootSource parent : (Frame.ofMountain p.initial).Node}
    {source : (Frame.ofMountain p.reduced).Node}
    (hColumn : rootSource.1.val = p.root.column) (hReal : Frame.Real source)
    (hSuffix : upperSuffix p.reduced source = upperSuffix p.initial rootSource)
    (hParent : (Frame.ofMountain p.initial).P rootSource = some parent) :
    ∃ reducedParent : (Frame.ofMountain p.reduced).Node,
      Frame.ref reducedParent = Frame.ref parent ∧
      (Frame.ofMountain p.reduced).cell reducedParent = (Frame.ofMountain p.initial).cell parent ∧
      reducedParent.1.val < p.root.column ∧
      (Frame.ofMountain p.reduced).P source = some reducedParent ∧
      RawRefEdge p.reduced (Frame.ref source) (Frame.ref parent) := by
  have hNormal := build_normal_of_success p.initial_build
  have hReducedNormal := build_normal_of_success p.reduced_build
  have hFixed : parent.1.val < p.root.column := by
    simpa only [hColumn] using Frame.P_column_lt hNormal.toOrdered hParent
  obtain ⟨oldUpper, hOldUpper⟩ := hNormal.upper_of_parent hParent
  obtain ⟨newUpper, hNewUpper, hCell⟩ :=
    (upperSuffix_upper_correspondence hSuffix).1 oldUpper hOldUpper
  have hParentRead : Canonical.cellAt p.reduced (Frame.ref parent) =
      .ok ((Frame.ofMountain p.initial).cell parent) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build
      (ref := Frame.ref parent) (hFixed.trans p.root_before_last)).symm.trans
        (cellAt_of_frame_node p.initial parent)
  obtain ⟨reducedParent, hRef, hParentCell⟩ := Canonical.frame_node_of_cellAt hParentRead
  have hSourceReal : Frame.Real rootSource := Frame.real_of_value_pos hNormal.toOrdered
    ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  obtain ⟨actualParent, hActual, _, _, hLeft⟩ := hNormal.upper_step rootSource oldUpper hSourceReal hOldUpper
  have he : actualParent = parent := Option.some.inj (hActual.symm.trans hParent)
  subst actualParent
  have hRaw : (Frame.ofMountain p.reduced).rawParent source = some reducedParent :=
    Frame.rawParent_eq_of_upper_left hNewUpper (by simpa only [hCell, hRef] using hLeft)
  exact ⟨reducedParent, hRef, hParentCell, (congrArg Ref.column hRef).trans_lt hFixed,
    (hReducedNormal.rawParent_eq_P hReal).symm.trans hRaw,
    by simpa only [hRef] using RawRefEdge.of_rawParent hRaw⟩

/-- At any cut at least Z, the real final-column frontier corresponds
to the original root-column frontier. Their stored fathers have the same
fixed original reference and full cell; parentless frontiers are actual
value-one terminals. No target numerical search is a premise.

When the source frontier is above the bad root its height is retained.
At the bad root the actual graft/effective height may differ, but lies
below Z and has the same upper barrier, so it is still the true frontier. -/
theorem Preparation.blocks_root_frontier_correspondence
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {cut : Row} (hOne : (1 : Row) ≤ cut) (hHigh : p.lastTop.row ≤ cut)
    {rootSource : (Frame.ofMountain p.initial).Node}
    (hColumn : rootSource.1.val = p.root.column)
    (hFrontier : Frame.frontierAt (build_normal_of_success p.initial_build).toOrdered
      cut hOne rootSource.1 = rootSource) :
    ∃ (hValid : MountainValid result) (target : (Frame.ofMountain result).Node),
      target.1.val = result.size - 1 ∧ Frame.Real target ∧
      Frame.frontierAt hValid.toOrdered cut hOne target.1 = target ∧
      (p.lastTop.row ≤ (Frame.ofMountain p.initial).height rootSource →
        (Frame.ofMountain result).height target = (Frame.ofMountain p.initial).height rootSource) ∧
      (∀ parent, (Frame.ofMountain p.initial).P rootSource = some parent →
        parent.1.val < p.root.column ∧ RawRefEdge result (Frame.ref target) (Frame.ref parent) ∧
        Canonical.cellAt result (Frame.ref parent) = .ok ((Frame.ofMountain p.initial).cell parent)) ∧
      ((Frame.ofMountain p.initial).P rootSource = none →
        (Frame.ofMountain result).upper target = none ∧
        (Frame.ofMountain result).rawParent target = none ∧
        (Frame.ofMountain result).value target = 1) := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.initial_build
  have hReducedNormal := build_normal_of_success p.reduced_build
  have hSpec := Frame.frontierAt_spec hNormal.toOrdered hOne rootSource.1
  have hRootReal : Frame.Real rootSource := hFrontier ▸ hSpec.2.1
  have hRootBelow : F.height rootSource ≤ cut := hFrontier ▸ hSpec.2.2.1
  have hRootBarrier : ∀ upper, F.upper rootSource = some upper → cut < F.height upper := by
    simpa only [hFrontier] using hSpec.2.2.2.2
  obtain ⟨g⟩ := p.root_geometry hLast
  have hRootColumn : g.rootNode.1 = rootSource.1 :=
    Fin.ext ((congrArg Ref.column g.root_ref).trans hColumn.symm)
  have hRootLow : F.height g.rootNode < p.lastTop.row := by
    change (F.cell g.rootNode).row < _
    rw [g.root_cell]
    exact p.root_row_lt_top hLast
  have hAfter : p.root.index ≤ rootSource.2.val := by
    have hi := index_le_of_frontier hNormal.toOrdered hOne hFrontier hRootColumn
      (hRootLow.le.trans hHigh)
    simpa only [show g.rootNode.2.val = p.root.index from congrArg Ref.index g.root_ref] using hi
  obtain ⟨source, hSourceColumn, hSourceReal, hSuffix, hSourceCase⟩ :=
    p.reduced_root_node_correspondence hLast g hColumn hAfter
  have hSourceBelow : G.height source ≤ cut := by
    rcases hSourceCase with ⟨_, hLow⟩ | hCell
    · exact hLow.le.trans hHigh
    · exact (congrArg Cell.row hCell).trans_le hRootBelow
  have hSourceHighRow : p.lastTop.row ≤ F.height rootSource → G.height source = F.height rootSource := by
    intro hRootHigh
    rcases hSourceCase with ⟨he, _⟩ | hCell
    · exact False.elim ((not_lt_of_ge hRootHigh) (he ▸ hRootLow))
    · exact congrArg Cell.row hCell
  have hSourceBarrier : ∀ upper, G.upper source = some upper → cut < G.height upper := by
    intro upper hUpper
    obtain ⟨oldUpper, hOldUpper, hOldCell⟩ :=
      (upperSuffix_upper_correspondence hSuffix.symm).1 upper hUpper
    exact (hRootBarrier oldUpper hOldUpper).trans_eq (congrArg Cell.row hOldCell)
  have hSourceNone : F.P rootSource = none → G.upper source = none := by
    intro hNone
    exact (upperSuffix_upper_correspondence hSuffix).2
      (normal_upper_none_of_parent_none hNormal hRootReal hNone)
  rcases p.blocks_final_history_of_run hLast hRun with ⟨_, he⟩ |
    ⟨_, _, _, _, _, state, history⟩
  · subst result
    refine ⟨p.reduced_valid, source, hSourceColumn, hSourceReal,
      Frame.frontierAt_eq_of_upper_barrier p.reduced_valid.toOrdered hOne hSourceBelow hSourceBarrier,
      hSourceHighRow, ?_, ?_⟩
    · intro parent hParent
      obtain ⟨reducedParent, hRef, hCell, hFixed, _, hEdge⟩ :=
        p.reduced_root_suffix_parent hColumn hSourceReal hSuffix hParent
      exact ⟨(congrArg Ref.column hRef).symm.trans_lt hFixed, hEdge,
        by simpa only [hRef, hCell] using cellAt_of_frame_node p.reduced reducedParent⟩
    · intro hNone
      have hTop := hSourceNone hNone
      exact ⟨hTop, Frame.rawParent_none_of_upper_none hTop,
        normal_value_one_of_upper_none hReducedNormal hSourceReal hTop⟩
  · have hRight : p.root.column < source.1.val := by
      have hSize := build_size p.reduced_build
      simp only [List.length_append, List.length_singleton] at hSize
      have hBefore := p.root_before_last
      omega
    obtain ⟨copy⟩ := state.prior_effective_occurrence history hLast hRight source.1.isLt
    obtain ⟨target, hRef, hCell, hTargetFrontier⟩ := copy.frontierAt_high_of_bounds
      hLast state.ambient_valid hOne hHigh hSourceReal hSourceBelow hSourceBarrier
    have hTargetColumn : target.1.val = result.size - 1 := by
      have hs := state.size_eq
      have hc : target.1.val = copy.outputRef.column := congrArg Ref.column hRef
      have hCopyCol : copy.outputRef.column =
          source.1.val + _ := copy.source_column
      change result.size = p.reduced.size + _ at hs
      omega
    have hTargetReal : Frame.Real target := by
      have hi : target.2.val = copy.read.outputIndex := congrArg Ref.index hRef
      change 0 < target.2.val
      rw [hi]
      exact copy.read.output_real hSourceReal
    refine ⟨state.ambient_valid, target, hTargetColumn, hTargetReal, hTargetFrontier, ?_, ?_, ?_⟩
    · intro hRootHigh
      have hSourceRow := hSourceHighRow hRootHigh
      change ((Frame.ofMountain result).cell target).row = _
      rw [hCell, copy.high_row hLast (hSourceRow.symm ▸ hRootHigh), hSourceRow]
    · intro parent hParent
      obtain ⟨reducedParent, hParentRef, hParentCell, hFixed, hSourceParent, _⟩ :=
        p.reduced_root_suffix_parent hColumn hSourceReal hSuffix hParent
      obtain ⟨hEdge, hParentRead⟩ := state.recorded_fixed_parent history hLast hSourceParent
        hRight source.1.isLt hFixed copy
      exact ⟨(congrArg Ref.column hParentRef).symm.trans_lt hFixed,
        by simpa only [hRef, hParentRef] using hEdge,
        by simpa only [hParentRef, hParentCell] using hParentRead⟩
    · intro hNone
      have hSourceTop := hSourceNone hNone
      have hTop := copy.top_upper_none hLast hSourceTop hRef
      exact ⟨hTop, Frame.rawParent_none_of_upper_none hTop,
        (congrArg Cell.value hCell).trans (copy.top_of_source_top hLast hSourceTop).2⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.upperSuffix_later_correspondence
#print axioms OmegaY.Expansion.upperSuffix_upper_correspondence
#print axioms OmegaY.Expansion.Preparation.reduced_root_node_correspondence
#print axioms OmegaY.Expansion.Preparation.reduced_root_suffix_parent
#print axioms OmegaY.Expansion.Preparation.blocks_root_frontier_correspondence
