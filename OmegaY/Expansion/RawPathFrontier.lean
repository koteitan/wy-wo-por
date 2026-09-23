/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawPathFrontier.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.FillRecordPath
import OmegaY.Expansion.RawNumericSuffix
import OmegaY.Forests.RefinedForestDepth

/-!
# Actual stored-reference paths in finite event forests

Once a raw path starts at an actual event frontier, raw parent closure keeps
every step at that frontier. Its exact number of physical stored edges is
therefore retained in the actual column forest, before numerical recovery.
This connects array-level root subdivisions to finite forest depth formulas.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem RawRefPath.event_frontier_steps {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered)
    (hRaw : (Frame.ofMountain mountain).RawRowGeometry)
    (hFather : (Frame.ofMountain mountain).RawFatherUpperBound)
    (hWidth : 0 < mountain.size) {bound event : Nat}
    {child parent : Ref} (path : RawRefPath mountain child parent)
    {u p : (Frame.ofMountain mountain).Node}
    (hU : Frame.ref u = child) (hP : Frame.ref p = parent)
    (hFront : eventFrontier hOrdered event u.1 = u) (hBound : u.1.val ≤ bound) :
    ∃ length, Forests.ParentSteps (eventParentMap hOrdered hWidth bound event)
      u.1.val p.1.val length ∧ eventFrontier hOrdered event p.1 = p := by
  induction path generalizing u with
  | refl ref =>
    have he : u = p := Executable.ref_injective _ (hU.trans hP.symm)
    subst u
    exact ⟨0, .nil _, hFront⟩
  | @cons child next parent edge tail ih =>
    have edgeCopy := edge
    obtain ⟨_, _, _, _, _, _, hRead⟩ := edgeCopy
    obtain ⟨q, hQRef, _⟩ := Canonical.frame_node_of_cellAt hRead
    have hEdge : (Frame.ofMountain mountain).rawParent u = some q := edge.rawParent hU hQRef
    have hFrontEdge : (Frame.ofMountain mountain).rawParent (eventFrontier hOrdered event u.1) =
        some q := by rw [hFront]; exact hEdge
    have hNextFront := eventFrontier_raw_parent_of_bound hOrdered hRaw hFather event u.1 hFrontEdge
    have hNextBound := (rawParent_column_lt hOrdered hEdge).le.trans hBound
    obtain ⟨length, hSteps, hEnd⟩ := ih hQRef hP hNextFront hNextBound
    have hMap : eventParentMap hOrdered hWidth bound event u.1.val = some q.1.val := by
      rw [eventParentMap_raw_at hOrdered hWidth event u.1 hBound, hFront, hEdge]
      rfl
    exact ⟨length + 1, .cons hMap hSteps, hEnd⟩

/-- The physical raw path determines its contribution to actual frontier
depths; no numerical P path, depth equality or length certificate is input. -/
theorem RawRefPath.event_depth {mountain : Mountain}
    (hOrdered : (Frame.ofMountain mountain).Ordered)
    (hRaw : (Frame.ofMountain mountain).RawRowGeometry)
    (hFather : (Frame.ofMountain mountain).RawFatherUpperBound)
    (hWidth : 0 < mountain.size) {bound event : Nat} (hBound : bound < mountain.size)
    {child parent : Ref} (path : RawRefPath mountain child parent)
    {u p : (Frame.ofMountain mountain).Node}
    (hU : Frame.ref u = child) (hP : Frame.ref p = parent)
    (hFront : eventFrontier hOrdered event u.1 = u) (hColumn : u.1.val ≤ bound) :
    ∃ length, Forests.ParentSteps (eventParentMap hOrdered hWidth bound event)
        u.1.val p.1.val length ∧
      eventFrontier hOrdered event p.1 = p ∧
      parentDepth (eventParentMap hOrdered hWidth bound event) u.1.val =
        parentDepth (eventParentMap hOrdered hWidth bound event) p.1.val + length := by
  obtain ⟨length, hSteps, hEnd⟩ := path.event_frontier_steps hOrdered hRaw hFather hWidth hU hP hFront hColumn
  exact ⟨length, hSteps, hEnd, hSteps.depth (eventParentMap_leftward hOrdered hWidth hBound event)⟩

/-- Actual expansion supplies all geometric hypotheses in the depth bridge.
The concrete path and its starting-frontier identification remain explicit. -/
theorem expandDiagram_raw_path_event_depth {input : List Nat} (hLegal : Canonical.Legal input)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram input copies = .ok mountain)
    (hWidth : 0 < mountain.size) {bound event : Nat} (hBound : bound < mountain.size)
    {child parent : Ref} (path : RawRefPath mountain child parent)
    {u p : (Frame.ofMountain mountain).Node}
    (hU : Frame.ref u = child) (hP : Frame.ref p = parent)
    (hFront : eventFrontier (expandDiagram_valid_of_success hLegal hRun).toOrdered event u.1 = u)
    (hColumn : u.1.val ≤ bound) :
    let hOrdered := (expandDiagram_valid_of_success hLegal hRun).toOrdered
    ∃ length, Forests.ParentSteps (eventParentMap hOrdered hWidth bound event)
        u.1.val p.1.val length ∧
      eventFrontier hOrdered event p.1 = p ∧
      parentDepth (eventParentMap hOrdered hWidth bound event) u.1.val =
        parentDepth (eventParentMap hOrdered hWidth bound event) p.1.val + length :=
  path.event_depth (expandDiagram_valid_of_success hLegal hRun).toOrdered
    (expandDiagram_raw_geometry hLegal hRun).rawRowGeometry
    (expandDiagram_raw_father_upper_bound hLegal hRun) hWidth hBound hU hP hFront hColumn

end OmegaY.Expansion

#print axioms OmegaY.Expansion.RawRefPath.event_frontier_steps
#print axioms OmegaY.Expansion.RawRefPath.event_depth
#print axioms OmegaY.Expansion.expandDiagram_raw_path_event_depth
