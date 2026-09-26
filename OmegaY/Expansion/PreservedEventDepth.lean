/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PreservedEventDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PreservedFrameNodes
import OmegaY.Expansion.RawPathFrontier

/-!
# Event forests and depths in a preserved complete prefix

Complete columns preserve both presence and absence of uppers and raw
parents. At the same cut, frontiers therefore name the same original
cells. Their raw event-parent maps and parent depths agree throughout the
preserved prefix. Event indices may differ; output Normal is not required.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem PreservesColumns.mapNode_upper_none {before after : Mountain}
    (h : PreservesColumns before after) {node : (Frame.ofMountain before).Node}
    (hNone : (Frame.ofMountain before).upper node = none) :
    (Frame.ofMountain after).upper (h.mapNode node) = none := by
  cases hUpper : (Frame.ofMountain after).upper (h.mapNode node) with
  | none => rfl
  | some upper =>
      have hColumn : upper.1.val < before.size := by
        rw [congrArg Fin.val (Frame.upper_spec hUpper).1, h.mapNode_column]
        exact node.1.isLt
      have hRead : Canonical.cellAt before (Frame.ref upper) = .ok ((Frame.ofMountain after).cell upper) :=
        (h.cellAt hColumn).symm.trans (Canonical.cellAt_of_frame_node after upper)
      obtain ⟨oldUpper, hOldRef, _⟩ := Canonical.frame_node_of_cellAt hRead
      have hUpperRef : Frame.ref upper = ⟨(Frame.ref node).column, (Frame.ref node).index + 1⟩ := by
        simp only [Frame.ref, Ref.mk.injEq]
        exact ⟨(congrArg Fin.val (Frame.upper_spec hUpper).1).trans (h.mapNode_column node),
          (Frame.upper_spec hUpper).2.trans (congrArg (· + 1) (h.mapNode_index node))⟩
      have hOldUpper : (Frame.ofMountain before).upper node = some oldUpper :=
        Frame.upper_of_refs rfl (hOldRef.trans hUpperRef)
      rw [hNone] at hOldUpper
      cases hOldUpper

theorem PreservesColumns.mapNode_upper_eq {before after : Mountain}
    (h : PreservesColumns before after) (node : (Frame.ofMountain before).Node) :
    (Frame.ofMountain after).upper (h.mapNode node) =
      ((Frame.ofMountain before).upper node).map h.mapNode := by
  cases hUpper : (Frame.ofMountain before).upper node with
  | none => exact h.mapNode_upper_none hUpper
  | some upper => exact h.mapNode_upper hUpper

/-- Raw parent absence is preserved too. Source ordered stored-leg validity
rules out a dangling old reference becoming valid only after appending. -/
theorem PreservesColumns.mapNode_rawParent_eq {before after : Mountain}
    (h : PreservesColumns before after) (hBefore : (Frame.ofMountain before).Ordered)
    (node : (Frame.ofMountain before).Node) :
    (Frame.ofMountain after).rawParent (h.mapNode node) =
      ((Frame.ofMountain before).rawParent node).map h.mapNode := by
  cases hParent : (Frame.ofMountain before).rawParent node with
  | some parent => exact h.mapNode_rawParent hParent
  | none =>
      cases hUpper : (Frame.ofMountain before).upper node with
      | none => exact Frame.rawParent_none_of_upper_none (h.mapNode_upper_none hUpper)
      | some upper =>
          cases hLeft : ((Frame.ofMountain before).cell upper).left with
          | none =>
              unfold Frame.rawParent
              rw [h.mapNode_upper hUpper]
              change (((Frame.ofMountain after).cell (h.mapNode upper)).left.bind
                (Frame.ofMountain after).lookup) = none
              rw [h.mapNode_cell, hLeft]
              rfl
          | some ref =>
              obtain ⟨parent, hLookup, _⟩ := hBefore.stored_valid upper ref hLeft
              have hSome : (Frame.ofMountain before).rawParent node = some parent := by
                unfold Frame.rawParent
                rw [hUpper]
                change (((Frame.ofMountain before).cell upper).left.bind
                  (Frame.ofMountain before).lookup) = some parent
                rw [hLeft]
                exact hLookup
              rw [hParent] at hSome
              cases hSome

/-- At a common cut the preserved original frontier is the actual target
frontier. No event enumeration or raw-parent closure is assumed here. -/
theorem PreservesColumns.mapNode_frontierAt {before after : Mountain}
    (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    {cut : Row} (hCut : (1 : Row) ≤ cut) (column : Fin (Frame.ofMountain before).width) :
    let old := frontierAt hBefore cut hCut column
    frontierAt hAfter cut hCut (h.mapNode old).1 = h.mapNode old := by
  dsimp only
  let old := frontierAt hBefore cut hCut column
  have hSpec := frontierAt_spec hBefore hCut column
  apply frontierAt_eq_of_upper_barrier hAfter hCut
    ((h.mapNode_height old).trans_le hSpec.2.2.1)
  intro upper hUpper
  rw [h.mapNode_upper_eq] at hUpper
  cases hOldUpper : (Frame.ofMountain before).upper old with
  | none => simp only [hOldUpper, Option.map_none] at hUpper; cases hUpper
  | some oldUpper =>
      have he : h.mapNode oldUpper = upper := Option.some.inj (by simpa only [hOldUpper, Option.map_some] using hUpper)
      rw [← he, h.mapNode_height]
      exact hSpec.2.2.2.2 oldUpper hOldUpper

theorem PreservesColumns.mapNode_eventFrontier {before after : Mountain}
    (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    {sourceEvent targetEvent : Nat}
    (hCut : (Frame.ofMountain after).eventCut targetEvent = (Frame.ofMountain before).eventCut sourceEvent)
    (column : Fin (Frame.ofMountain before).width) :
    let old := eventFrontier hBefore sourceEvent column
    eventFrontier hAfter targetEvent (h.mapNode old).1 = h.mapNode old := by
  dsimp only
  unfold eventFrontier
  simpa only [hCut] using h.mapNode_frontierAt hBefore hAfter
    ((Frame.ofMountain before).eventCut_one_le sourceEvent) column

/-- Actual raw event-parent maps agree on every old column at the same
cut, including actual `none` parents. -/
theorem PreservesColumns.eventParentMap_at_preserved {before after : Mountain}
    (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    (hSourceWidth : 0 < before.size) (hTargetWidth : 0 < after.size)
    {sourceEvent targetEvent : Nat}
    (hCut : (Frame.ofMountain after).eventCut targetEvent = (Frame.ofMountain before).eventCut sourceEvent)
    {column : Nat} (hColumn : column < before.size) :
    eventParentMap hAfter hTargetWidth (after.size - 1) targetEvent column =
      eventParentMap hBefore hSourceWidth (before.size - 1) sourceEvent column := by
  let sourceColumn : Fin (Frame.ofMountain before).width := ⟨column, hColumn⟩
  let old := eventFrontier hBefore sourceEvent sourceColumn
  have hOldColumn : old.1.val = column := congrArg Fin.val (eventFrontier_spec hBefore sourceEvent sourceColumn).1
  have hNewColumn : (h.mapNode old).1.val = column := (h.mapNode_column old).trans hOldColumn
  have hTargetColumn : column < after.size := hNewColumn ▸ (h.mapNode old).1.isLt
  have hTargetBound : (h.mapNode old).1.val ≤ after.size - 1 := by rw [hNewColumn]; omega
  have hSourceBound : sourceColumn.val ≤ before.size - 1 := by change column ≤ before.size - 1; omega
  have hTargetMap := eventParentMap_raw_at hAfter hTargetWidth targetEvent (h.mapNode old).1 hTargetBound
  rw [hNewColumn, h.mapNode_eventFrontier hBefore hAfter hCut sourceColumn,
    h.mapNode_rawParent_eq hBefore old] at hTargetMap
  rw [hTargetMap, eventParentMap_raw_at hBefore hSourceWidth sourceEvent sourceColumn hSourceBound]
  change (((Frame.ofMountain before).rawParent old).map h.mapNode).map (fun p => p.1.val) =
    ((Frame.ofMountain before).rawParent old).map (fun p => p.1.val)
  cases hParent : (Frame.ofMountain before).rawParent old with
  | none => rfl
  | some parent => simp only [Option.map_some, h.mapNode_column]

/-- Complete-prefix preservation gives absolute depth equality at any
pair of events having the same cut. No endpoint depth is an input. -/
theorem PreservesColumns.event_parentDepth {before after : Mountain}
    (h : PreservesColumns before after)
    (hBefore : (Frame.ofMountain before).Ordered) (hAfter : (Frame.ofMountain after).Ordered)
    (hSourceWidth : 0 < before.size) (hTargetWidth : 0 < after.size)
    {sourceEvent targetEvent : Nat}
    (hCut : (Frame.ofMountain after).eventCut targetEvent = (Frame.ofMountain before).eventCut sourceEvent)
    {column : Nat} (hColumn : column < before.size) :
    parentDepth (eventParentMap hAfter hTargetWidth (after.size - 1) targetEvent) column =
      parentDepth (eventParentMap hBefore hSourceWidth (before.size - 1) sourceEvent) column := by
  let sourceMap : ParentMap := eventParentMap hBefore hSourceWidth (before.size - 1) sourceEvent
  let targetMap : ParentMap := eventParentMap hAfter hTargetWidth (after.size - 1) targetEvent
  have hSourceLeft : Leftward sourceMap := eventParentMap_leftward hBefore hSourceWidth
    (by change before.size - 1 < before.size; omega) sourceEvent
  have hTargetLeft : Leftward targetMap := eventParentMap_leftward hAfter hTargetWidth
    (by change after.size - 1 < after.size; omega) targetEvent
  have hMaps : ∀ c, c < before.size → targetMap c = sourceMap c := fun c hc =>
    h.eventParentMap_at_preserved hBefore hAfter hSourceWidth hTargetWidth hCut hc
  change parentDepth targetMap column = parentDepth sourceMap column
  induction column using Nat.strongRecOn with
  | ind column ih =>
      cases hParent : sourceMap column with
      | none =>
          have hNone : targetMap column = none := (hMaps column hColumn).trans hParent
          rw [parentDepth_none hNone, parentDepth_none hParent]
      | some parent =>
          have hSome : targetMap column = some parent := (hMaps column hColumn).trans hParent
          rw [parentDepth_some hTargetLeft hSome, parentDepth_some hSourceLeft hParent,
            ih parent (hSourceLeft hParent) ((hSourceLeft hParent).trans hColumn)]

end OmegaY.Expansion

#print axioms OmegaY.Expansion.PreservesColumns.mapNode_rawParent_eq
#print axioms OmegaY.Expansion.PreservesColumns.mapNode_eventFrontier
#print axioms OmegaY.Expansion.PreservesColumns.eventParentMap_at_preserved
#print axioms OmegaY.Expansion.PreservesColumns.event_parentDepth
