/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualIteratedBoundaryDepth.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualIteratedLowBoundary
import OmegaY.Expansion.RawPathFrontier
import OmegaY.Expansion.BlocksRawGeometry
import OmegaY.Expansion.BlocksRawFatherBound

/-!
# Actual event depth at every iterated low-root boundary

An event frontier includes its event cut. A strict `below cap` selector is
therefore the frontier at the event immediately preceding the actual cap
event. The unchanged original root-upper cell proves that this cap remains
an event in every completed-block mountain. The initial frontier identity,
the raw parent path, and all raw geometric invariants are derived from the
actual outer execution, not supplied as assumptions.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- The result of applying the actual low-root boundary path at its correct
strict-before event. This is an output packet, not an invariant assumed of
an arbitrary copied mountain. -/
structure LowBoundaryEventDepth {front : List Nat} {last : Nat}
    (p : Preparation front last) (mountain : Mountain)
    (root rootUpper : (Frame.ofMountain p.initial).Node) where
  valid : MountainValid mountain
  width_pos : 0 < mountain.size
  event : Nat
  length : Nat
  selected : (Frame.ofMountain mountain).Node
  originalRoot : (Frame.ofMountain mountain).Node
  event_before_last : event < (Frame.ofMountain mountain).lastEvent
  next_cut : (Frame.ofMountain mountain).eventCut (event + 1) =
    (Frame.ofMountain p.initial).height rootUpper
  selected_column : selected.1.val = mountain.size - 1
  root_reference : Frame.ref originalRoot = Frame.ref root
  root_cell : (Frame.ofMountain mountain).cell originalRoot = (Frame.ofMountain p.initial).cell root
  selected_below : below mountain (mountain.size - 1) ((Frame.ofMountain p.initial).height rootUpper) =
    .ok (Frame.ref selected)
  selected_frontier : eventFrontier valid.toOrdered event selected.1 = selected
  root_frontier : eventFrontier valid.toOrdered event originalRoot.1 = originalRoot
  steps : Forests.ParentSteps (eventParentMap valid.toOrdered width_pos (mountain.size - 1) event)
    (mountain.size - 1) p.root.column length
  depth_eq : parentDepth (eventParentMap valid.toOrdered width_pos (mountain.size - 1) event)
      (mountain.size - 1) =
    parentDepth (eventParentMap valid.toOrdered width_pos (mountain.size - 1) event) p.root.column + length
  depth_le : parentDepth (eventParentMap valid.toOrdered width_pos (mountain.size - 1) event) p.root.column ≤
    parentDepth (eventParentMap valid.toOrdered width_pos (mountain.size - 1) event) (mountain.size - 1)

private theorem low_depth_upper_height_lt {F : Frame} (hF : F.Ordered) {u upper : F.Node}
    (hUpper : F.upper u = some upper) : F.height u < F.height upper := by
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    exact hF.rows_strict c (show i.val < i.val + 1 by omega)
  · cases hUpper

/-- For every actual finite outer-loop execution and every original real
root strictly below the bad root, the last-column strict-cap frontier has
a genuine event-parent path to that original root's frontier. Its exact
path length is the resulting nonnegative depth increment. -/
theorem Preparation.blocks_low_boundary_event_depth
    {front : List Nat} {last : Nat} (p : Preparation front last) (hLast : 1 < last)
    {copies : Nat} {result : Mountain}
    (hRun : (forIn (List.range copies) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok result)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper) :
    Nonempty (LowBoundaryEventDepth p result root rootUpper) := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain result
  obtain ⟨output, hOutput, hReady, reference, cell, hBelow, _, hPath⟩ :=
    p.blocks_low_boundary_path hLast hRootReal hRootColumn hBefore hRootUpper copies
  have he : output = result := Except.ok.inj (hOutput.symm.trans hRun)
  subst output
  have hValid := hReady.valid
  have hRootLeft : root.1.val < front.length := hRootColumn ▸ p.root_before_last
  have hUpperLeft : rootUpper.1.val < front.length :=
    (congrArg Fin.val (Frame.upper_spec hRootUpper).1).trans_lt hRootLeft
  have hReducedSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hReducedSize
  have hRootReadReduced : Canonical.cellAt p.reduced (Frame.ref root) = .ok (F.cell root) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hRootLeft).symm.trans
      (Canonical.cellAt_of_frame_node p.initial root)
  have hUpperReadReduced : Canonical.cellAt p.reduced (Frame.ref rootUpper) = .ok (F.cell rootUpper) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hUpperLeft).symm.trans
      (Canonical.cellAt_of_frame_node p.initial rootUpper)
  have hRootRead : Canonical.cellAt result (Frame.ref root) = .ok (F.cell root) :=
    (hReady.base_preserved.cellAt (by change root.1.val < p.reduced.size; omega)).trans hRootReadReduced
  have hUpperRead : Canonical.cellAt result (Frame.ref rootUpper) = .ok (F.cell rootUpper) :=
    (hReady.base_preserved.cellAt (by change rootUpper.1.val < p.reduced.size; omega)).trans hUpperReadReduced
  obtain ⟨originalRoot, hRootRef, hRootCell⟩ := Canonical.frame_node_of_cellAt hRootRead
  obtain ⟨capNode, hCapRef, hCapCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hWidth : 0 < result.size := (Nat.zero_le originalRoot.1.val).trans_lt originalRoot.1.isLt
  have hBound : result.size - 1 < result.size := by omega
  have hCapReal : Frame.Real capNode := by
    have hi : capNode.2.val = rootUpper.2.val := congrArg Ref.index hCapRef
    change 0 < capNode.2.val
    rw [hi]
    exact upper_real hRootUpper
  have hCapOne : (1 : Row) < F.height rootUpper :=
    (Frame.one_le_height (build_normal_of_success p.initial_build).toOrdered hRootReal).trans_lt
      (low_depth_upper_height_lt (build_normal_of_success p.initial_build).toOrdered hRootUpper)
  obtain ⟨capEvent, hCapEvent, hCapRow⟩ := Frame.real_height_at_event hValid.toOrdered hCapReal
  change capEvent ≤ G.lastEvent at hCapEvent
  have hCapRow' : G.eventCut capEvent = F.height rootUpper :=
    hCapRow.trans (congrArg Cell.row hCapCell)
  have hCapPositive : 0 < capEvent := by
    by_contra hn
    have hz : capEvent = 0 := by omega
    rw [hz, G.eventCut_zero] at hCapRow'
    exact (lt_irrefl (1 : Row)) (by simpa only [← hCapRow'] using hCapOne)
  let event := capEvent - 1
  have hEvent : event < G.lastEvent := by dsimp only [event]; omega
  have hNext : event + 1 = capEvent := by dsimp only [event]; omega
  have hNextCut : G.eventCut (event + 1) = F.height rootUpper := by rw [hNext]; exact hCapRow'
  let lastColumn : Fin G.width := ⟨result.size - 1, hBound⟩
  let selected := eventFrontier hValid.toOrdered event lastColumn
  have hSelectedColumn : selected.1.val = result.size - 1 :=
    congrArg Fin.val (eventFrontier_spec hValid.toOrdered event lastColumn).1
  have hSelectedBelow : below result (result.size - 1) (F.height rootUpper) =
      .ok (Frame.ref selected) := by
    have h := eventFrontier_below_next_cut hValid hEvent lastColumn
    change below result (result.size - 1) (G.eventCut (event + 1)) = .ok (Frame.ref selected) at h
    simpa only [hNextCut] using h
  have hSelectedRef : Frame.ref selected = reference :=
    Except.ok.inj (hSelectedBelow.symm.trans hBelow)
  have hSelectedFront : eventFrontier hValid.toOrdered event selected.1 = selected := by
    rw [(eventFrontier_spec hValid.toOrdered event lastColumn).1]
  have hRaw := (p.blocks_raw_geometry_of_run hLast hRun).rawRowGeometry
  have hFather := (p.blocks_raw_father_bound_of_run hLast hRun).rawFatherUpperBound
  obtain ⟨length, hSteps, hRootFront, hDepth⟩ := hPath.event_depth hValid.toOrdered hRaw hFather
    hWidth hBound hSelectedRef hRootRef hSelectedFront (by rw [hSelectedColumn])
  have hRootColumn' : originalRoot.1.val = p.root.column := (congrArg Ref.column hRootRef).trans hRootColumn
  have hSteps' : Forests.ParentSteps (eventParentMap hValid.toOrdered hWidth (result.size - 1) event)
      (result.size - 1) p.root.column length := by
    simpa only [hSelectedColumn, hRootColumn'] using hSteps
  have hDepth' : parentDepth (eventParentMap hValid.toOrdered hWidth (result.size - 1) event)
      (result.size - 1) =
      parentDepth (eventParentMap hValid.toOrdered hWidth (result.size - 1) event) p.root.column + length := by
    simpa only [hSelectedColumn, hRootColumn'] using hDepth
  exact ⟨{
    valid := hValid
    width_pos := hWidth
    event := event
    length := length
    selected := selected
    originalRoot := originalRoot
    event_before_last := hEvent
    next_cut := hNextCut
    selected_column := hSelectedColumn
    root_reference := hRootRef
    root_cell := hRootCell
    selected_below := hSelectedBelow
    selected_frontier := hSelectedFront
    root_frontier := hRootFront
    steps := hSteps'
    depth_eq := hDepth'
    depth_le := by rw [hDepth']; exact Nat.le_add_right _ _ }⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.blocks_low_boundary_event_depth
