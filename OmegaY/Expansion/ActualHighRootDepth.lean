/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualHighRootDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualHighRootFrontier
import OmegaY.Expansion.HighEventTailSampling
import OmegaY.Expansion.RawPathFrontier
import OmegaY.Expansion.PreservedEventDepth

/-!
# Root-boundary frontiers in the reduced source and actual high event forests

The root column and its strictly earlier columns survive the decrement
unchanged. Actual reads and executable search locality transport the root
frontier certificate to the reduced source, before any depth comparison.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- The same complete column selects the same actual index at a common
cut, even when the surrounding mountains have different event lists. -/
theorem frontierAt_of_same_column {before after : Mountain}
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    {cut : Row} (hOne : (1 : Row) ≤ cut)
    {source : (Frame.ofMountain before).Node} {target : (Frame.ofMountain after).Node}
    (hFrontier : frontierAt hBefore cut hOne source.1 = source)
    (hRef : Frame.ref target = Frame.ref source)
    (hColumns : after[source.1.val]? = before[source.1.val]?) :
    frontierAt hAfter cut hOne target.1 = target := by
  have hSourceSpec := frontierAt_spec hBefore hOne source.1
  have hSourceBelow : (Frame.ofMountain before).height source ≤ cut := hFrontier ▸ hSourceSpec.2.2.1
  have hSourceBarrier : ∀ upper, (Frame.ofMountain before).upper source = some upper →
      cut < (Frame.ofMountain before).height upper := by
    simpa only [hFrontier] using hSourceSpec.2.2.2.2
  have hCell : (Frame.ofMountain after).cell target = (Frame.ofMountain before).cell source := by
    apply Except.ok.inj
    exact (cellAt_of_frame_node after target).symm.trans
      (by rw [hRef, cellAt_eq_of_column_eq hColumns]; exact cellAt_of_frame_node before source)
  apply frontierAt_eq_of_upper_barrier hAfter hOne
  · exact (congrArg Cell.row hCell).trans_le hSourceBelow
  · intro upper hUpper
    have hUpperRef : Frame.ref upper = ⟨source.1.val, source.2.val + 1⟩ := by
      have hc := congrArg Ref.column hRef
      have hi := congrArg Ref.index hRef
      simp only [Frame.ref, Ref.mk.injEq] at hRef ⊢
      exact ⟨(congrArg Fin.val (upper_spec hUpper).1).trans hc,
        (upper_spec hUpper).2.trans (congrArg (· + 1) hi)⟩
    have hOldRead : Canonical.cellAt before ⟨source.1.val, source.2.val + 1⟩ =
        .ok ((Frame.ofMountain after).cell upper) := by
      rw [← cellAt_eq_of_column_eq (ref := ⟨source.1.val, source.2.val + 1⟩) hColumns]
      rw [← hUpperRef]
      exact cellAt_of_frame_node after upper
    obtain ⟨oldUpper, hOldRef, hOldCell⟩ := Canonical.frame_node_of_cellAt hOldRead
    have hOldUpper : (Frame.ofMountain before).upper source = some oldUpper :=
      Frame.upper_of_refs rfl hOldRef
    exact (hSourceBarrier oldUpper hOldUpper).trans_eq (congrArg Cell.row hOldCell)

/-- The same root-frontier theorem expressed entirely in the frozen
reduced source. Its numerical parent correspondence is proved using the
actual search's strict-left locality, not supplied as an additional input. -/
theorem Preparation.blocks_reduced_root_frontier_correspondence
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
      (p.lastTop.row ≤ (Frame.ofMountain p.reduced).height rootSource →
        (Frame.ofMountain result).height target = (Frame.ofMountain p.reduced).height rootSource) ∧
      (∀ parent, (Frame.ofMountain p.reduced).P rootSource = some parent →
        parent.1.val < p.root.column ∧ RawRefEdge result (Frame.ref target) (Frame.ref parent) ∧
        Canonical.cellAt result (Frame.ref parent) = .ok ((Frame.ofMountain p.reduced).cell parent)) ∧
      ((Frame.ofMountain p.reduced).P rootSource = none →
        (Frame.ofMountain result).upper target = none ∧
        (Frame.ofMountain result).rawParent target = none ∧
        (Frame.ofMountain result).value target = 1) := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hNormal := build_normal_of_success p.initial_build
  have hReducedNormal := build_normal_of_success p.reduced_build
  have hRootBefore : rootSource.1.val < front.length := hColumn ▸ p.root_before_last
  have hColumns : ∀ c, c ≤ rootSource.1.val → p.initial[c]? = p.reduced[c]? :=
    fun c hc => build_changed_last_preserves_prefix p.initial_build p.reduced_build (hc.trans_lt hRootBefore)
  have hRootRead : Canonical.cellAt p.initial (Frame.ref rootSource) = .ok (G.cell rootSource) :=
    (cellAt_eq_of_column_eq (hColumns _ le_rfl)).trans (cellAt_of_frame_node p.reduced rootSource)
  obtain ⟨oldRoot, hOldRef, hOldCell⟩ := Canonical.frame_node_of_cellAt hRootRead
  have hOldColumn : oldRoot.1.val = p.root.column := (congrArg Ref.column hOldRef).trans hColumn
  have hOldFrontier : frontierAt hNormal.toOrdered cut hOne oldRoot.1 = oldRoot :=
    frontierAt_of_same_column hReducedNormal.toOrdered hNormal.toOrdered hOne hFrontier hOldRef
      (hColumns _ le_rfl)
  obtain ⟨hValid, target, hTargetColumn, hReal, hTargetFrontier, hHighRow, hParents, hNone⟩ :=
    p.blocks_root_frontier_correspondence hLast hRun hOne hHigh hOldColumn hOldFrontier
  have hSearch : findParent p.initial (Frame.ref oldRoot) = findParent p.reduced (Frame.ref rootSource) := by
    rw [hOldRef]
    exact findParent_eq_of_columns hColumns
  refine ⟨hValid, target, hTargetColumn, hReal, hTargetFrontier, ?_, ?_, ?_⟩
  · intro hRootHigh
    simpa only [Frame.height, hOldCell] using hHighRow (by simpa only [Frame.height, hOldCell] using hRootHigh)
  · intro parent hParent
    have hActual : findParent p.initial (Frame.ref oldRoot) = .ok (Frame.ref parent) :=
      hSearch.trans ((Executable.findParent_ref_iff hReducedNormal.toOrdered rootSource parent).mpr hParent)
    obtain ⟨oldParent, hOldParent, hParentRef⟩ :=
      (Executable.findParent_iff hNormal.toOrdered oldRoot (Frame.ref parent)).mp hActual
    obtain ⟨hFixed, hEdge, hRead⟩ := hParents oldParent hOldParent
    have hParentColumn : parent.1.val < front.length :=
      ((congrArg Ref.column hParentRef).symm.trans_lt hFixed).trans p.root_before_last
    have hParentCell : F.cell oldParent = G.cell parent := by
      apply Except.ok.inj
      exact (cellAt_of_frame_node p.initial oldParent).symm.trans (by
        rw [hParentRef, build_changed_last_preserves_ref p.initial_build p.reduced_build hParentColumn]
        exact cellAt_of_frame_node p.reduced parent)
    exact ⟨(congrArg Ref.column hParentRef).symm.trans_lt hFixed,
      by simpa only [hParentRef] using hEdge,
      by
        have hRead' : cellAt result (Frame.ref parent) = .ok (F.cell oldParent) := by
          simpa only [hParentRef] using hRead
        exact hRead'.trans (congrArg Except.ok hParentCell)⟩
  · intro hNoParent
    have hSourceSearch : (findParent p.reduced (Frame.ref rootSource)).toOption = none := by
      simpa only [hNoParent, Option.map_none] using Executable.findParent_toOption hReducedNormal.toOrdered rootSource
    have hMapNone : (F.P oldRoot).map Frame.ref = none :=
      (Executable.findParent_toOption hNormal.toOrdered oldRoot).symm.trans
        ((congrArg Except.toOption hSearch).trans hSourceSearch)
    have hOldNone : F.P oldRoot = none := by
      cases hp : F.P oldRoot with
      | none => rfl
      | some parent => simp only [hp, Option.map_some] at hMapNone; cases hMapNone
    exact hNone hOldNone

/-- At any pair of actual events with the same high cut, the new
boundary forest depth equals the reduced root-column forest depth.
Only the genuine run supplies root-frontier and fixed-prefix agreement.
The proof is the two actual parent recurrences, or zero in the terminal
case; it does not assume the depth balance as a packet field. -/
theorem Preparation.blocks_root_depth_at_equal_events
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    (hValid : MountainValid result) (hSourceWidth : 0 < p.reduced.size)
    (hTargetWidth : 0 < result.size) {sourceEvent targetEvent : Nat}
    (hCut : (Frame.ofMountain result).eventCut targetEvent =
      (Frame.ofMountain p.reduced).eventCut sourceEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent) :
    parentDepth (eventParentMap hValid.toOrdered hTargetWidth (result.size - 1) targetEvent)
        (result.size - 1) =
      parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
        hSourceWidth (p.reduced.size - 1) sourceEvent) p.root.column := by
  let F := Frame.ofMountain p.reduced
  let T := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  obtain ⟨ready, _⟩ := p.blocks_high_root_boundary_of_success hLast hRun
  obtain ⟨rootNodes, hRootNodes, _⟩ := cellAt_ok_iff.mp p.restored_root
  have hRootBound : p.root.column < p.reduced.size := (Array.getElem?_eq_some_iff.mp hRootNodes).1
  let rootColumn : Fin F.width := ⟨p.root.column, hRootBound⟩
  let rootSource := eventFrontier hNormal.toOrdered sourceEvent rootColumn
  have hRootColumn : rootSource.1.val = p.root.column := rfl
  have hRootFrontier : frontierAt hNormal.toOrdered (F.eventCut sourceEvent)
      (F.eventCut_one_le sourceEvent) rootSource.1 = rootSource := rfl
  obtain ⟨_, target, hColumn, _, hFrontier, _, hParents, hNone⟩ :=
    p.blocks_reduced_root_frontier_correspondence hLast hRun (F.eventCut_one_le sourceEvent)
      hHigh hRootColumn hRootFrontier
  have hTargetFront : eventFrontier hValid.toOrdered targetEvent target.1 = target := by
    unfold eventFrontier
    simpa only [hCut] using hFrontier
  let sourceMap := eventParentMap hNormal.toOrdered hSourceWidth (p.reduced.size - 1) sourceEvent
  let targetMap := eventParentMap hValid.toOrdered hTargetWidth (result.size - 1) targetEvent
  have hSourceLeft : Leftward sourceMap := eventParentMap_leftward hNormal.toOrdered hSourceWidth
    (by change p.reduced.size - 1 < p.reduced.size; omega) sourceEvent
  have hTargetLeft : Leftward targetMap := eventParentMap_leftward hValid.toOrdered hTargetWidth
    (by change result.size - 1 < result.size; omega) targetEvent
  have hSourceAt : sourceMap p.root.column = (F.P rootSource).map (fun parent => parent.1.val) :=
    hNormal.eventParentMap_at hSourceWidth sourceEvent rootColumn (by change p.root.column ≤ p.reduced.size - 1; omega)
  have hTargetAt : targetMap (result.size - 1) = (T.rawParent target).map (fun parent => parent.1.val) := by
    have hm := eventParentMap_raw_at hValid.toOrdered hTargetWidth targetEvent target.1
      (show target.1.val ≤ result.size - 1 from hColumn.le)
    simpa only [hColumn, hTargetFront] using hm
  change parentDepth targetMap (result.size - 1) = parentDepth sourceMap p.root.column
  cases hp : F.P rootSource with
  | none =>
      have ht : T.rawParent target = none := (hNone hp).2.1
      have hsMap : sourceMap p.root.column = none := by simpa only [hp, Option.map_none] using hSourceAt
      have htMap : targetMap (result.size - 1) = none := by simpa only [ht, Option.map_none] using hTargetAt
      rw [parentDepth_none htMap, parentDepth_none hsMap]
  | some parent =>
      obtain ⟨_, hEdge, hParentRead⟩ := hParents parent hp
      obtain ⟨targetParent, hParentRef, _⟩ := Canonical.frame_node_of_cellAt hParentRead
      have hRaw : T.rawParent target = some targetParent := hEdge.rawParent rfl hParentRef
      have hParentColumn : targetParent.1.val = parent.1.val := congrArg Ref.column hParentRef
      have hsMap : sourceMap p.root.column = some parent.1.val := by
        simpa only [hp, Option.map_some] using hSourceAt
      have htMap : targetMap (result.size - 1) = some parent.1.val := by
        simpa only [hRaw, Option.map_some, hParentColumn] using hTargetAt
      have hFixedDepth : parentDepth targetMap parent.1.val = parentDepth sourceMap parent.1.val :=
        ready.base_preserved.event_parentDepth hNormal.toOrdered hValid.toOrdered
          hSourceWidth hTargetWidth hCut parent.1.isLt
      rw [parentDepth_some hTargetLeft htMap, parentDepth_some hSourceLeft hsMap, hFixedDepth]

/-- Every actual source high event receives a target event from the
executed high-tail sampling, and the two root/boundary depths agree.
The caller supplies neither a target event nor a depth correspondence. -/
theorem Preparation.blocks_high_root_depth
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {sourceEvent : Nat} (hSourceEvent : sourceEvent ≤ (Frame.ofMountain p.reduced).lastEvent)
    (hHigh : p.lastTop.row ≤ (Frame.ofMountain p.reduced).eventCut sourceEvent) :
    ∃ (hValid : MountainValid result) (hSourceWidth : 0 < p.reduced.size)
      (hTargetWidth : 0 < result.size) (targetEvent : Nat),
      (Frame.ofMountain result).highEventStart p.lastTop.row ≤ targetEvent ∧
      targetEvent ≤ (Frame.ofMountain result).lastEvent ∧
      (p.blocks_high_event_sampling hLast hRun).sample targetEvent = sourceEvent ∧
      (Frame.ofMountain result).eventCut targetEvent =
        (Frame.ofMountain p.reduced).eventCut sourceEvent ∧
      parentDepth (eventParentMap hValid.toOrdered hTargetWidth (result.size - 1) targetEvent)
          (result.size - 1) =
        parentDepth (eventParentMap (build_normal_of_success p.reduced_build).toOrdered
          hSourceWidth (p.reduced.size - 1) sourceEvent) p.root.column := by
  obtain ⟨ready, _⟩ := p.blocks_high_root_boundary_of_success hLast hRun
  obtain ⟨rootNodes, hRootNodes, _⟩ := cellAt_ok_iff.mp p.restored_root
  have hRootBound := (Array.getElem?_eq_some_iff.mp hRootNodes).1
  have hSourceWidth : 0 < p.reduced.size := (Nat.zero_le p.root.column).trans_lt hRootBound
  have hTargetWidth : 0 < result.size := hSourceWidth.trans_le ready.base_preserved.size_le
  obtain ⟨targetEvent, hStart, hEnd, hSample, hCut⟩ :=
    p.blocks_high_event_correspondence hLast hRun hSourceEvent hHigh
  exact ⟨ready.valid, hSourceWidth, hTargetWidth, targetEvent, hStart, hEnd, hSample, hCut,
    p.blocks_root_depth_at_equal_events hLast hRun ready.valid hSourceWidth hTargetWidth hCut hHigh⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.frontierAt_of_same_column
#print axioms OmegaY.Expansion.Preparation.blocks_reduced_root_frontier_correspondence
#print axioms OmegaY.Expansion.Preparation.blocks_root_depth_at_equal_events
#print axioms OmegaY.Expansion.Preparation.blocks_high_root_depth
