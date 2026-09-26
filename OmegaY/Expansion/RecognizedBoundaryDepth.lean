/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RecognizedBoundaryDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RecognizedPrefix
import OmegaY.Expansion.ActualIteratedBoundaryDepth
import OmegaY.Expansion.InitialBoundaryFrontierPath

/-!
# Earlier boundary events inside a recognized strict-left prefix

The actual completed-block boundary has a proved raw path at each low
root's strict cap. Strict-left numerical induction reconstructs that
completed prefix, so canonical event projection carries the path to every
earlier event. No recognition of the current copied column is used.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- The entire earlier event interval, not just the strict-cap selector,
has boundary depth at least the original root column's depth. -/
theorem Preparation.blocks_low_boundary_depth_le_of_left_recognition
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {start ambient : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok start)
    (hPreserved : PreservesColumns start ambient)
    (hAmbient : (Frame.ofMountain ambient).Ordered)
    (hKnown : ∀ (node parent : (Frame.ofMountain ambient).Node),
      node.1.val < start.size → Real node →
      (Frame.ofMountain ambient).rawParent node = some parent →
        (Frame.ofMountain ambient).P node = some parent)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper)
    (hStartValid : MountainValid start) (hWidth : 0 < start.size)
    (event : Nat)
    (hCut : (Frame.ofMountain start).eventCut event <
      (Frame.ofMountain p.initial).height rootUpper) :
    parentDepth (eventParentMap hStartValid.toOrdered hWidth (start.size - 1) event) p.root.column ≤
      parentDepth (eventParentMap hStartValid.toOrdered hWidth (start.size - 1) event) (start.size - 1) := by
  obtain ⟨values, _, hBuild⟩ := p.blocks_reconstruct_of_left_recognition
    hLast hRun hPreserved hAmbient hKnown
  have hNormal := build_normal_of_success hBuild
  obtain ⟨data⟩ := p.blocks_low_boundary_event_depth hLast hRun
    hRootReal hRootColumn hBefore hRootUpper
  have hOrder : event ≤ data.event := by
    by_contra hNot
    have hRows := (Frame.ofMountain start).eventCut_monotone
      (show data.event + 1 ≤ event by omega)
    rw [data.next_cut] at hRows
    exact (not_lt_of_ge hRows) hCut
  have hRawPath := p.blocks_low_selected_path hLast hRun hRootReal hRootColumn
    hBefore hRootUpper data.selected_below
  have hPath : ParentPath (Frame.ofMountain start) data.selected data.originalRoot :=
    hRawPath.toParentPath hNormal.toOrdered (bound := start.size)
      (fun _ _ hReal => hNormal.rawParent_eq_P hReal) rfl data.root_reference
      (data.selected_frontier ▸ (eventFrontier_spec hNormal.toOrdered data.event data.selected.1).2.1)
      data.selected.1.isLt
  have hProjected := build_parent_path_event_projection hBuild hWidth hOrder
    data.event_before_last.le data.selected_frontier hPath
  have hColumnBound : (eventFrontier hNormal.toOrdered event data.selected.1).1.val ≤ start.size - 1 := by
    rw [(eventFrontier_spec hNormal.toOrdered event data.selected.1).1, data.selected_column]
  have hRootColumn' : data.originalRoot.1.val = p.root.column :=
    (congrArg Ref.column data.root_reference).trans hRootColumn
  have hMapped := hNormal.parentPath_eventParentMap hWidth rfl hColumnBound hProjected
  have hBound : start.size - 1 < start.size := by omega
  rcases hMapped with hEqual | hAncestor
  · have hColumns := congrArg (fun node : (Frame.ofMountain start).Node => node.1.val) hEqual
    simp only [(eventFrontier_spec hNormal.toOrdered event data.selected.1).1,
      (eventFrontier_spec hNormal.toOrdered event data.originalRoot.1).1,
      data.selected_column, hRootColumn'] at hColumns
    rw [hColumns]
  · have hDepth := ancestor_depth_lt
      (eventParentMap_leftward hNormal.toOrdered hWidth hBound event) hAncestor
    simpa only [(eventFrontier_spec hNormal.toOrdered event data.selected.1).1,
      (eventFrontier_spec hNormal.toOrdered event data.originalRoot.1).1,
      data.selected_column, hRootColumn'] using hDepth.le

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_low_boundary_depth_le_of_left_recognition
