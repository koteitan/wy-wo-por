/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/TotalFrontier.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.TotalRawFatherBound

/-!
# Actual finite frontier events of every expanded mountain

Both raw B and the father-upper bound now come from the executed expansion.
They close the geometry-to-synchronous-backfill interface on the actual
finite union of row heights. Numerical first-smaller recognition and
descent between successive expansions remain separate.
-/

namespace OmegaY.Expansion

open Canonical Geometry

theorem expandDiagram_valid_of_success {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result) :
    MountainValid result := by
  obtain ⟨actual, hActual, hValid⟩ := expandDiagram_total hLegal copies
  have he : actual = result := Except.ok.inj (hActual.symm.trans hRun)
  exact he ▸ hValid

/-- At every height cut, the physical raw father of a frontier node is
exactly its own column's frontier, not just some smaller row in that column. -/
theorem expandDiagram_frontier_parent {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result)
    {cut : Row} (hCut : (1 : Row) ≤ cut) (column : Fin (Frame.ofMountain result).width)
    {parent : (Frame.ofMountain result).Node}
    (hParent : (Frame.ofMountain result).rawParent
      (Frame.frontierAt (expandDiagram_valid_of_success hLegal hRun).toOrdered cut hCut column) =
        some parent) :
    Frame.frontierAt (expandDiagram_valid_of_success hLegal hRun).toOrdered cut hCut parent.1 = parent :=
  Frame.frontierAt_raw_parent_of_bound (expandDiagram_valid_of_success hLegal hRun).toOrdered
    (expandDiagram_raw_geometry hLegal hRun).rawRowGeometry
    (expandDiagram_raw_father_upper_bound hLegal hRun) hCut column hParent

/-- The geometry of the entire actual event list has no outstanding copied
row, parent-closure, numerical-parent, or normality hypothesis. -/
theorem expandDiagram_eventFrontier_geometry {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result)
    (hWidth : 0 < result.size) {bound : Nat} (hBound : bound < result.size) :
    Frame.FrontierGeometry (Frame.ofMountain result)
      (Frame.eventFrontierNat (expandDiagram_valid_of_success hLegal hRun).toOrdered hWidth)
      (Frame.ofMountain result).eventCut bound 0 (Frame.ofMountain result).lastEvent :=
  Frame.eventFrontier_geometry_of_raw_bound (expandDiagram_valid_of_success hLegal hRun).toOrdered
    (expandDiagram_raw_geometry hLegal hRun).rawRowGeometry
    (expandDiagram_raw_father_upper_bound hLegal hRun) hWidth hBound

/-- Positive sums at common actual row events supply synchronous backfill
for every actual expansion. No NumericSuffix is claimed. -/
theorem expandDiagram_event_synchronousBackfill {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result)
    (hWidth : 0 < result.size) {bound : Nat} (hBound : bound < result.size)
    (initial : ZeroY.ParentMap) :
    Forests.SynchronousBackfill
      ((Frame.ofMountain result).frontierForests initial
        (Frame.eventFrontierNat (expandDiagram_valid_of_success hLegal hRun).toOrdered hWidth) bound)
      ((Frame.ofMountain result).frontierValue
        (Frame.eventFrontierNat (expandDiagram_valid_of_success hLegal hRun).toOrdered hWidth))
      (Frame.frontierMoves
        (Frame.eventFrontierNat (expandDiagram_valid_of_success hLegal hRun).toOrdered hWidth))
      bound 0 (Frame.ofMountain result).lastEvent :=
  expandDiagram_synchronousBackfill hLegal hRun
    (expandDiagram_eventFrontier_geometry hLegal hRun hWidth hBound) initial

/-- The actual candidate reached after a column advances is identified by
its old raw father's column at the new event. -/
theorem expandDiagram_event_moving_candidate {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result)
    {event : Nat} (hEvent : event < (Frame.ofMountain result).lastEvent)
    (column : Fin (Frame.ofMountain result).width)
    (hChanged : Frame.eventFrontier (expandDiagram_valid_of_success hLegal hRun).toOrdered
        (event + 1) column ≠
      Frame.eventFrontier (expandDiagram_valid_of_success hLegal hRun).toOrdered event column) :
    ∃ parent, (Frame.ofMountain result).rawParent
        (Frame.eventFrontier (expandDiagram_valid_of_success hLegal hRun).toOrdered event column) =
          some parent ∧
      (Frame.ofMountain result).Q
        (Frame.eventFrontier (expandDiagram_valid_of_success hLegal hRun).toOrdered (event + 1) column) =
          some (Frame.eventFrontier (expandDiagram_valid_of_success hLegal hRun).toOrdered
            (event + 1) parent.1) :=
  (expandDiagram_equations hLegal hRun).1.eventFrontier_moving_candidate
    (expandDiagram_valid_of_success hLegal hRun) hEvent column hChanged

theorem expandDiagram_event_terminal_one {values : List Nat} (hLegal : Legal values)
    {copies : Nat} {result : Mountain} (hRun : expandDiagram values copies = .ok result)
    (column : Fin (Frame.ofMountain result).width) :
    (Frame.ofMountain result).value
      (Frame.eventFrontier (expandDiagram_valid_of_success hLegal hRun).toOrdered
        (Frame.ofMountain result).lastEvent column) = 1 :=
  MountainTops.eventFrontier_last_value (expandDiagram_valid_of_success hLegal hRun)
    (expandDiagram_equations hLegal hRun).2 column

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_valid_of_success
#print axioms OmegaY.Expansion.expandDiagram_frontier_parent
#print axioms OmegaY.Expansion.expandDiagram_eventFrontier_geometry
#print axioms OmegaY.Expansion.expandDiagram_event_synchronousBackfill
#print axioms OmegaY.Expansion.expandDiagram_event_moving_candidate
#print axioms OmegaY.Expansion.expandDiagram_event_terminal_one
