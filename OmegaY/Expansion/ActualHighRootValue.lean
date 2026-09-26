/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighRootValue.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighRootDepth

/-!
# Actual root-boundary values at high cuts

At a shared cut the source root frontier and actual boundary frontier
have the same fixed parent. Their raw B laws force equal upper heights,
even when the lower heights differ below Z. Upward induction on the
strictly decreasing source value, starting at the true value-one top,
then compares the actual backfill equations. No target numerical parent
recognition or inference from forest-depth equality is used.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

private theorem root_value_upper_lt {F : Frame} (hF : F.Ordered) {u upper : F.Node}
    (hUpper : F.upper u = some upper) : F.height u < F.height upper := by
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    exact hF.rows_strict c (show i.val < i.val + 1 by omega)
  · cases hUpper

private theorem root_value_frontier_self {F : Frame} (hF : F.Ordered)
    (u : F.Node) (hOne : (1 : Row) ≤ F.height u) :
    frontierAt hF (F.height u) hOne u.1 = u := by
  apply frontierAt_eq_of_upper_barrier hF hOne le_rfl
  intro upper hUpper
  exact root_value_upper_lt hF hUpper

/-- Actual corresponding root/boundary frontiers have the same numerical
value. Both frontiers are real selectors at the supplied common high cut;
their lower rows need not be equal. All target sums and raw laws come from
the actual outer execution. -/
theorem Preparation.blocks_root_value_at_frontiers
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    (hValid : MountainValid result)
    {cut : Row} (hOne : (1 : Row) ≤ cut) (hHigh : p.lastTop.row ≤ cut)
    {rootSource : (Frame.ofMountain p.reduced).Node} {target : (Frame.ofMountain result).Node}
    (hColumn : rootSource.1.val = p.root.column)
    (hFrontier : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      cut hOne rootSource.1 = rootSource)
    (hTargetColumn : target.1.val = result.size - 1)
    (hTargetFrontier : frontierAt hValid.toOrdered cut hOne target.1 = target) :
    (Frame.ofMountain result).value target = (Frame.ofMountain p.reduced).value rootSource := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hRaw := (p.blocks_raw_geometry_of_run hLast hRun).rawRowGeometry
  obtain ⟨equationsResult, hEquationsRun, _, hSums, _⟩ := p.blocks_equations hLast copies
  have he : equationsResult = result := Except.ok.inj (hEquationsRun.symm.trans hRun)
  subst equationsResult
  generalize hValue : F.value rootSource = value
  induction value using Nat.strongRecOn generalizing rootSource target cut with
  | ind value ih =>
    have hSourceSpec := frontierAt_spec hNormal.toOrdered hOne rootSource.1
    have hSourceReal : Real rootSource := hFrontier ▸ hSourceSpec.2.1
    have hSourceBelow : F.height rootSource ≤ cut := hFrontier ▸ hSourceSpec.2.2.1
    have hSourceBarrier : ∀ upper, F.upper rootSource = some upper → cut < F.height upper := by
      simpa only [hFrontier] using hSourceSpec.2.2.2.2
    have hTargetSpec := frontierAt_spec hValid.toOrdered hOne target.1
    have hTargetReal : Real target := hTargetFrontier ▸ hTargetSpec.2.1
    have hTargetBelow : T.height target ≤ cut := hTargetFrontier ▸ hTargetSpec.2.2.1
    have hTargetBarrier : ∀ upper, T.upper target = some upper → cut < T.height upper := by
      simpa only [hTargetFrontier] using hTargetSpec.2.2.2.2
    obtain ⟨_, actual, hActualColumn, _, hActualFrontier, _, hParents, hNone⟩ :=
      p.blocks_reduced_root_frontier_correspondence hLast hRun hOne hHigh hColumn hFrontier
    have hActualEq : actual = target := by
      have hc : actual.1 = target.1 := Fin.ext (hActualColumn.trans hTargetColumn.symm)
      rw [hc, hTargetFrontier] at hActualFrontier
      exact hActualFrontier.symm
    subst actual
    cases hParent : F.P rootSource with
    | none =>
      have hPositive := hNormal.real_positive rootSource hSourceReal
      have hSourceOne : F.value rootSource = 1 := by
        by_contra hn
        have hLarge : 1 < F.value rootSource := by dsimp only [F] at *; omega
        obtain ⟨parent, hp⟩ := hNormal.parent_exists hLarge
        rw [hParent] at hp
        cases hp
      exact (hNone hParent).2.2.trans (hSourceOne.symm.trans hValue)
    | some parent =>
      obtain ⟨_, hEdge, hParentRead⟩ := hParents parent hParent
      obtain ⟨targetParent, hParentRef, hParentCell⟩ := Canonical.frame_node_of_cellAt hParentRead
      have hTargetParent : T.rawParent target = some targetParent := hEdge.rawParent rfl hParentRef
      obtain ⟨sourceUpper, hSourceUpper⟩ := hNormal.upper_of_parent hParent
      obtain ⟨sourceParent, hSourceParent, hSourceB, hDifference, _⟩ :=
        hNormal.upper_step rootSource sourceUpper hSourceReal hSourceUpper
      have hSourceParentEq : sourceParent = parent := Option.some.inj (hSourceParent.symm.trans hParent)
      subst sourceParent
      change F.height sourceUpper = Row.B (F.height rootSource) (F.height parent) at hSourceB
      change F.value sourceUpper = F.value rootSource - F.value parent at hDifference
      obtain ⟨targetUpper, hTargetUpper, _⟩ := rawParent_spec hTargetParent
      obtain ⟨rawParent, hRawParent, _, hParentRow, hTargetB⟩ :=
        hRaw target targetUpper hTargetReal hTargetUpper
      have hRawParentEq : rawParent = targetParent := Option.some.inj (hRawParent.symm.trans hTargetParent)
      subst rawParent
      change T.height targetUpper = Row.B (T.height target) (T.height targetParent) at hTargetB
      have hParentHeight : T.height targetParent = F.height parent := congrArg Cell.row hParentCell
      have hParentValue : T.value targetParent = F.value parent := congrArg Cell.value hParentCell
      have hUpperHeight : T.height targetUpper = F.height sourceUpper := by
        rw [hTargetB, hParentHeight, hSourceB]
        exact B_equal_at_common_frontier (hParentHeight ▸ hParentRow)
          (P_height_le hNormal.toOrdered hParent) hTargetBelow hSourceBelow
          (by simpa only [hTargetB, hParentHeight] using hTargetBarrier targetUpper hTargetUpper)
          (by simpa only [hSourceB] using hSourceBarrier sourceUpper hSourceUpper)
      have hSourceUpperHigh : p.lastTop.row ≤ F.height sourceUpper :=
        hHigh.trans (hSourceBarrier sourceUpper hSourceUpper).le
      have hUpperOne : (1 : Row) ≤ F.height sourceUpper :=
        hOne.trans (hSourceBarrier sourceUpper hSourceUpper).le
      have hTargetUpperFrontier : frontierAt hValid.toOrdered (F.height sourceUpper)
          hUpperOne targetUpper.1 = targetUpper := by
        have hAt := root_value_frontier_self hValid.toOrdered targetUpper (hUpperHeight.symm ▸ hUpperOne)
        change frontierAt hValid.toOrdered (T.height targetUpper) _ targetUpper.1 = targetUpper at hAt
        simpa only [hUpperHeight] using hAt
      have hSmall : F.value sourceUpper < value := by
        have hPos := (P_value hNormal.toOrdered hParent).1
        have hLess := (P_value hNormal.toOrdered hParent).2
        dsimp only [F] at *
        omega
      have hUpperValue : T.value targetUpper = F.value sourceUpper :=
        ih (F.value sourceUpper) hSmall hUpperOne hSourceUpperHigh
          ((congrArg Fin.val (upper_spec hSourceUpper).1).trans hColumn)
          (root_value_frontier_self hNormal.toOrdered sourceUpper hUpperOne)
          ((congrArg Fin.val (upper_spec hTargetUpper).1).trans hTargetColumn)
          hTargetUpperFrontier rfl
      obtain ⟨sumParent, hSumParent, _, _, _, hSum, _⟩ :=
        hSums.rawParent_upper hValid hTargetReal hTargetUpper
      have hSumParentEq : sumParent = targetParent := Option.some.inj (hSumParent.symm.trans hTargetParent)
      subst sumParent
      have hSourceLess := (P_value hNormal.toOrdered hParent).2
      rw [hSum, hUpperValue, hParentValue]
      dsimp only [F, T] at *
      omega

/-- A high root source frontier selects an actual last-column frontier
with equal value, including the zero-block reduced mountain. No target
frontier or value comparison is supplied by the caller. -/
theorem Preparation.blocks_high_root_value
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {cut : Row} (hOne : (1 : Row) ≤ cut) (hHigh : p.lastTop.row ≤ cut)
    {rootSource : (Frame.ofMountain p.reduced).Node}
    (hColumn : rootSource.1.val = p.root.column)
    (hFrontier : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      cut hOne rootSource.1 = rootSource) :
    ∃ (hValid : MountainValid result) (target : (Frame.ofMountain result).Node),
      target.1.val = result.size - 1 ∧ Real target ∧
      frontierAt hValid.toOrdered cut hOne target.1 = target ∧
      (Frame.ofMountain result).value target = (Frame.ofMountain p.reduced).value rootSource := by
  obtain ⟨hValid, target, hTargetColumn, hReal, hTargetFrontier, _⟩ :=
    p.blocks_reduced_root_frontier_correspondence hLast hRun hOne hHigh hColumn hFrontier
  exact ⟨hValid, target, hTargetColumn, hReal, hTargetFrontier,
    p.blocks_root_value_at_frontiers hLast hRun hValid hOne hHigh hColumn hFrontier
      hTargetColumn hTargetFrontier⟩

/-- The same value identity using a root-column node of the original
mountain. Its whole cell and frontier are transported through the actual
decrement's unchanged root column. -/
theorem Preparation.blocks_initial_root_value_at_frontiers
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    (hValid : MountainValid result)
    {cut : Row} (hOne : (1 : Row) ≤ cut) (hHigh : p.lastTop.row ≤ cut)
    {source : (Frame.ofMountain p.initial).Node} {target : (Frame.ofMountain result).Node}
    (hColumn : source.1.val = p.root.column)
    (hFrontier : frontierAt (build_normal_of_success p.initial_build).toOrdered
      cut hOne source.1 = source)
    (hTargetColumn : target.1.val = result.size - 1)
    (hTargetFrontier : frontierAt hValid.toOrdered cut hOne target.1 = target) :
    (Frame.ofMountain result).value target = (Frame.ofMountain p.initial).value source := by
  have hBefore : source.1.val < front.length := hColumn ▸ p.root_before_last
  have hRead : cellAt p.reduced (Frame.ref source) = .ok ((Frame.ofMountain p.initial).cell source) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hBefore).symm.trans
      (cellAt_of_frame_node p.initial source)
  obtain ⟨reducedSource, hRef, hCell⟩ := Canonical.frame_node_of_cellAt hRead
  have hReducedFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered
      cut hOne reducedSource.1 = reducedSource :=
    frontierAt_of_same_column (build_normal_of_success p.initial_build).toOrdered
      (build_normal_of_success p.reduced_build).toOrdered hOne hFrontier hRef
      (build_changed_last_preserves_prefix p.initial_build p.reduced_build hBefore).symm
  exact (p.blocks_root_value_at_frontiers hLast hRun hValid hOne hHigh
    ((congrArg Ref.column hRef).trans hColumn) hReducedFront hTargetColumn hTargetFrontier).trans
      (congrArg Cell.value hCell)

/-- The strict selector below Z has exactly the original bad-root value.
This also covers the case where Z itself is a real root-column row: the
selector remains below Z, so it is not confused with the frontier at Z. -/
theorem Preparation.blocks_highest_reference_value
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result) :
    ∃ reference cell,
      below result (result.size - 1) p.lastTop.row = .ok reference ∧
      cellAt result reference = .ok cell ∧ cell.row < p.lastTop.row ∧
      cell.value = p.rootCell.value := by
  let F := Frame.ofMountain p.initial
  let T := Frame.ofMountain result
  have hNormal := build_normal_of_success p.initial_build
  obtain ⟨g⟩ := p.root_geometry hLast
  obtain ⟨eqResult, hEqRun, ready, hSums, _⟩ := p.blocks_equations hLast copies
  have he : eqResult = result := Except.ok.inj (hEqRun.symm.trans hRun)
  subst eqResult
  have hValid := ready.valid
  cases hParent : F.P g.rootNode with
  | none =>
    obtain ⟨terminal, hBelow, _, _, hOne, _, _, hLow⟩ :=
      p.blocks_parentless_highest_of_run hLast hRun g hParent
    have hSourceOne : F.value g.rootNode = 1 := by
      have hPositive := hNormal.real_positive g.rootNode g.root_real
      by_contra hn
      have hLarge : 1 < F.value g.rootNode := by dsimp only [F] at *; omega
      obtain ⟨parent, hp⟩ := hNormal.parent_exists hLarge
      rw [hParent] at hp
      cases hp
    exact ⟨Frame.ref terminal, T.cell terminal, hBelow, cellAt_of_frame_node result terminal,
      hLow, hOne.trans (hSourceOne.symm.trans (congrArg Cell.value g.root_cell))⟩
  | some parent =>
    obtain ⟨_, reference, cell, hBelow, hRead, hLow, hEdge, hParentRead⟩ :=
      p.blocks_highest_edge_of_run hLast hRun g hParent
    obtain ⟨target, hTargetRef, hTargetCell⟩ := Canonical.frame_node_of_cellAt hRead
    obtain ⟨targetParent, hParentRef, hParentCell⟩ := Canonical.frame_node_of_cellAt hParentRead
    have hTargetParent : T.rawParent target = some targetParent := hEdge.rawParent hTargetRef hParentRef
    have hRootOne : (1 : Row) ≤ F.height g.rootNode := one_le_height hNormal.toOrdered g.root_real
    have hRootLow : F.height g.rootNode < p.lastTop.row := by
      change (F.cell g.rootNode).row < _
      rw [g.root_cell]
      exact p.root_row_lt_top hLast
    have hZOne : (1 : Row) < p.lastTop.row := hRootOne.trans_lt hRootLow
    have hWidth : 0 < result.size := by
      have hOld := g.rootNode.1.isLt
      have hInitialSize := build_size p.initial_build
      have hReducedSize := build_size p.reduced_build
      have hPreserve := ready.base_preserved.size_le
      change g.rootNode.1.val < p.initial.size at hOld
      simp only [List.length_append, List.length_singleton] at hInitialSize hReducedSize
      omega
    have hLastBound : result.size - 1 < result.size := by omega
    obtain ⟨actualRef, actualCell, hActual, hActualRead, hActualColumn, _, _, hPositive⟩ :=
      below_above_one_total hValid hLastBound hZOne
    have hRefEq : actualRef = reference := Except.ok.inj (hActual.symm.trans hBelow)
    subst actualRef
    have hCellEq : actualCell = cell := Except.ok.inj
      ((cellAt_ok_iff.mpr (lookup_ok_iff.mp hActualRead)).symm.trans hRead)
    subst actualCell
    have hTargetColumn : target.1.val = result.size - 1 :=
      (congrArg Ref.column hTargetRef).trans hActualColumn
    have hPositiveTarget : 0 < T.value target := by
      change 0 < (T.cell target).value
      rw [hTargetCell]
      exact hPositive
    have hTargetReal : Real target := real_of_value_pos hValid.toOrdered hPositiveTarget
    have hTargetLow : T.height target < p.lastTop.row :=
      (congrArg Cell.row hTargetCell).trans_lt hLow
    obtain ⟨sourceUpper, hSourceUpper⟩ := hNormal.upper_of_parent hParent
    obtain ⟨found, hFound, hSourceB, hDifference, _⟩ :=
      hNormal.upper_step g.rootNode sourceUpper g.root_real hSourceUpper
    have hFoundEq : found = parent := Option.some.inj (hFound.symm.trans hParent)
    subst found
    change F.height sourceUpper = Row.B (F.height g.rootNode) (F.height parent) at hSourceB
    change F.value sourceUpper = F.value g.rootNode - F.value parent at hDifference
    have hSourceUpperHigh : p.lastTop.row ≤ F.height sourceUpper := by
      have hD := father_upper_bound_nodes hNormal g.lower_parent g.lower_upper hSourceUpper
      change (F.cell g.topNode).row ≤ F.height sourceUpper at hD
      have hTopCell : F.cell g.topNode = p.lastTop := g.top_cell
      rw [hTopCell] at hD
      exact hD
    obtain ⟨targetUpper, hTargetUpper, _⟩ := rawParent_spec hTargetParent
    have hUpperRef : Frame.ref targetUpper = ⟨reference.column, reference.index + 1⟩ := by
      exact congrArg₂ Ref.mk
        ((congrArg Fin.val (upper_spec hTargetUpper).1).trans (congrArg Ref.column hTargetRef))
        ((upper_spec hTargetUpper).2.trans (congrArg (· + 1) (congrArg Ref.index hTargetRef)))
    have hUpperRead : cellAt result ⟨reference.column, reference.index + 1⟩ = .ok (T.cell targetUpper) := by
      rw [← hUpperRef]
      exact cellAt_of_frame_node result targetUpper
    have hTargetUpperHigh : p.lastTop.row ≤ T.height targetUpper := below_parent_upper_bound_at hBelow hUpperRead
    obtain ⟨rawParent, hRawParent, _, hParentRow, hTargetB⟩ :=
      (p.blocks_raw_geometry_of_run hLast hRun).rawRowGeometry target targetUpper hTargetReal hTargetUpper
    have hRawEq : rawParent = targetParent := Option.some.inj (hRawParent.symm.trans hTargetParent)
    subst rawParent
    change T.height targetUpper = Row.B (T.height target) (T.height targetParent) at hTargetB
    have hParentHeight : T.height targetParent = F.height parent := congrArg Cell.row hParentCell
    have hParentValue : T.value targetParent = F.value parent := congrArg Cell.value hParentCell
    have hBelowBoth : max (T.height target) (F.height g.rootNode) < p.lastTop.row :=
      max_lt hTargetLow hRootLow
    have hUpperHeight : T.height targetUpper = F.height sourceUpper := by
      rw [hTargetB, hParentHeight, hSourceB]
      exact B_equal_at_common_frontier (hParentHeight ▸ hParentRow)
        (P_height_le hNormal.toOrdered hParent) (le_max_left _ _) (le_max_right _ _)
        (by simpa only [hTargetB, hParentHeight] using hBelowBoth.trans_le hTargetUpperHigh)
        (by simpa only [hSourceB] using hBelowBoth.trans_le hSourceUpperHigh)
    have hUpperOne : (1 : Row) ≤ F.height sourceUpper := hZOne.le.trans hSourceUpperHigh
    have hTargetUpperFrontier : frontierAt hValid.toOrdered (F.height sourceUpper) hUpperOne
        targetUpper.1 = targetUpper := by
      have hAt := root_value_frontier_self hValid.toOrdered targetUpper (hUpperHeight.symm ▸ hUpperOne)
      change frontierAt hValid.toOrdered (T.height targetUpper) _ _ = targetUpper at hAt
      simpa only [hUpperHeight] using hAt
    have hUpperValue : T.value targetUpper = F.value sourceUpper :=
      p.blocks_initial_root_value_at_frontiers hLast hRun hValid hUpperOne hSourceUpperHigh
        ((congrArg Fin.val (upper_spec hSourceUpper).1).trans (congrArg Ref.column g.root_ref))
        (root_value_frontier_self hNormal.toOrdered sourceUpper hUpperOne)
        ((congrArg Fin.val (upper_spec hTargetUpper).1).trans hTargetColumn) hTargetUpperFrontier
    obtain ⟨sumParent, hSumParent, _, _, _, hSum, _⟩ := hSums.rawParent_upper hValid hTargetReal hTargetUpper
    have hSumEq : sumParent = targetParent := Option.some.inj (hSumParent.symm.trans hTargetParent)
    subst sumParent
    have hValue : T.value target = F.value g.rootNode := by
      rw [hSum, hUpperValue, hParentValue]
      have hLess := (P_value hNormal.toOrdered hParent).2
      dsimp only [F, T] at *
      omega
    exact ⟨reference, cell, hBelow, hRead, hLow,
      (congrArg Cell.value hTargetCell).symm.trans (hValue.trans (congrArg Cell.value g.root_cell))⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_root_value_at_frontiers
#print axioms OmegaY.Expansion.Preparation.blocks_high_root_value
#print axioms OmegaY.Expansion.Preparation.blocks_initial_root_value_at_frontiers
#print axioms OmegaY.Expansion.Preparation.blocks_highest_reference_value
