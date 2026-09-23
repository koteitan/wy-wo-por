/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CanonicalEventProjection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CanonicalFrontierInitial
import OmegaY.Forests.EventProjection
import OmegaY.Geometry.RowShadow

/-!
# Actual source-parent projection between canonical mountain events

A successful concrete source build supplies numeric recovery, synchronous
backfill, and leftward frontier forests. A later numerical parent edge
therefore projects to a genuine numerical parent path at any earlier event.
Its endpoint is the earlier frontier in the later parent's column, not an
assertion that the later physical parent already occurs at the earlier cut.

The source-level statements below take the concrete build and actual P
reads. They have no abstract NumericSuffix, backfill, path, or barrier input.
Nothing here asserts that an expansion output is already canonical.
-/

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

/-- A source event-map edge identifies its actual typed numerical parent,
including the exact frontier node rather than only its column number. -/
theorem Normal.eventParentMap_some {F : Frame} (hF : F.Normal) (hWidth : 0 < F.width)
    {bound event child found : Nat} (hBound : bound < F.width) (hc : child ≤ bound)
    (hMap : eventParentMap hF.toOrdered hWidth bound event child = some found) :
    F.P (eventFrontierNat hF.toOrdered hWidth event child) =
      some (eventFrontierNat hF.toOrdered hWidth event found) := by
  have hFound : found < child := eventParentMap_leftward hF.toOrdered hWidth hBound event hMap
  have hChildWidth : child < F.width := hc.trans_lt hBound
  have hFoundWidth : found < F.width := hFound.trans hChildWidth
  rw [hF.eventParentMap_at hWidth event ⟨child, hChildWidth⟩ hc] at hMap
  rw [eventFrontierNat_eq hF.toOrdered hWidth event hChildWidth,
    eventFrontierNat_eq hF.toOrdered hWidth event hFoundWidth]
  cases hParent : F.P (eventFrontier hF.toOrdered event ⟨child, hChildWidth⟩) with
  | none => simp only [hParent, Option.map_none] at hMap; cases hMap
  | some parent =>
      simp only [hParent, Option.map_some, Option.some.injEq] at hMap
      have hColumn : parent.1 = (⟨found, hFoundWidth⟩ : Fin F.width) := Fin.ext hMap
      have hFront := hF.eventFrontier_parent event ⟨child, hChildWidth⟩ hParent
      rw [hColumn] at hFront
      exact congrArg some hFront.symm

/-- Lift a nonempty actual event-map ancestor path to typed numerical P
edges. Leftwardness derives every intermediate valid column read. -/
theorem Normal.parentPath_of_eventParentMap_ancestor {F : Frame} (hF : F.Normal)
    (hWidth : 0 < F.width) {bound event child found : Nat}
    (hBound : bound < F.width) (hc : child ≤ bound)
    (hPath : Ancestor (eventParentMap hF.toOrdered hWidth bound event) child found) :
    ParentPath F (eventFrontierNat hF.toOrdered hWidth event child)
      (eventFrontierNat hF.toOrdered hWidth event found) := by
  induction hPath with
  | single edge => exact .cons (hF.eventParentMap_some hWidth hBound hc edge) (.refl _)
  | @tail middle last path edge ih =>
      have hMiddle := ancestor_lt (eventParentMap_leftward hF.toOrdered hWidth hBound event) path
      exact ih.trans (.cons (hF.eventParentMap_some hWidth hBound (by omega) edge) (.refl _))

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry ZeroY ZeroY.Forest

section Built

variable {input : List Nat} {mountain : Mountain}
variable (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)

include hWidth


/-- Actual source map projection. All generic event assumptions are
constructed from the successful canonical build inside this proof. -/
theorem build_event_parent_map_projection
    {bound start event : Nat} (hBound : bound < mountain.size)
    (hOrder : start ≤ event) (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (column : Fin (Frame.ofMountain mountain).width) (hColumn : column.val ≤ bound) {parent : (Frame.ofMountain mountain).Node}
    (hParent : (Frame.ofMountain mountain).P (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event column) = some parent) :
    Forests.BarrierPath (Frame.eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound start)
      (Frame.eventValues (build_normal_of_success hBuild).toOrdered hWidth start)
      ((Frame.ofMountain mountain).value (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event column)) column.val parent.1.val := by
  have hNormal := build_normal_of_success hBuild
  let front := Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth
  let forests := (Frame.ofMountain mountain).frontierForests (Frame.bottomCandidateMap bound) front bound
  let values := (Frame.ofMountain mountain).frontierValue front
  have hColumns : ∀ event column, column ≤ bound → (front event column).1.val = column := by
    intro event column hColumn
    dsimp only [front]
    rw [Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth event (hColumn.trans_lt hBound)]
    rfl
  have hLeft : ∀ r, start ≤ r → r ≤ (Frame.ofMountain mountain).lastEvent → Leftward (forests r) := by
    intro r _ _
    exact Frame.frontierForests_leftward (build_normal_of_success hBuild).toOrdered
      (Frame.bottomCandidateMap_leftward bound) hColumns r
  have hFullNumeric : Forests.NumericSuffix forests values bound 0 (Frame.ofMountain mountain).lastEvent :=
    build_eventFrontier_numeric_full hBuild hWidth hBound
  have hNumeric : Forests.NumericSuffix forests values bound start (Frame.ofMountain mountain).lastEvent := by
    intro r _ hFinish c hc
    exact hFullNumeric r (Nat.zero_le _) hFinish c hc
  have hFullBackfill : Forests.SynchronousBackfill forests values
      (Frame.frontierMoves front) bound 0 (Frame.ofMountain mountain).lastEvent :=
    build_eventFrontier_synchronousBackfill hBuild hWidth hBound (Frame.bottomCandidateMap bound)
  have hBackfill : Forests.SynchronousBackfill forests values
      (Frame.frontierMoves front) bound start (Frame.ofMountain mountain).lastEvent := {
    stationary := fun r _ hr c hc hStay => hFullBackfill.stationary r (Nat.zero_le _) hr c hc hStay
    moving := fun r _ hr c hc hMove => hFullBackfill.moving r (Nat.zero_le _) hr c hc hMove
    synchronous := fun r _ hr c z hc hz hSame =>
      hFullBackfill.synchronous r (Nat.zero_le _) hr c z hc hz hSame }
  have hMap : forests (event + 1) column.val = some parent.1.val := by
    change Frame.eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event column.val = some parent.1.val
    rw [hNormal.eventParentMap_at hWidth event column hColumn, hParent]
    rfl
  have hProjection := Forests.event_parent_projection hLeft hNumeric hBackfill hOrder hEvent hColumn hMap
  change Forests.BarrierPath (Frame.eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound start)
    (Frame.eventValues (build_normal_of_success hBuild).toOrdered hWidth start)
    (Frame.eventValues (build_normal_of_success hBuild).toOrdered hWidth event column.val) column.val parent.1.val at hProjection
  rw [Frame.eventValues_at (build_normal_of_success hBuild).toOrdered hWidth event column] at hProjection
  exact hProjection

/-- Typed source-parent projection and the numerical barrier at every
actual earlier record before the endpoint. The final parent occurrence is
the earlier frontier in the later parent's column. -/
theorem build_event_parent_projection
    {bound start event : Nat} (hBound : bound < mountain.size)
    (hOrder : start ≤ event) (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (column : Fin (Frame.ofMountain mountain).width) (hColumn : column.val ≤ bound) {parent : (Frame.ofMountain mountain).Node}
    (hParent : (Frame.ofMountain mountain).P (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event column) = some parent) :
    Frame.ParentPath (Frame.ofMountain mountain) (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start column)
      (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start parent.1) ∧ parent.1.val < column.val ∧
      ∀ z : (Frame.ofMountain mountain).Node, Frame.ParentPath (Frame.ofMountain mountain) (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start column) z →
        parent.1.val < z.1.val →
        Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start z.1 = z ∧ z.1.val ≤ bound ∧
          (Frame.ofMountain mountain).value (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event column) ≤ (Frame.ofMountain mountain).value z := by
  have hNormal := build_normal_of_success hBuild
  have hPath := build_event_parent_map_projection hBuild hWidth hBound hOrder hEvent column hColumn hParent
  have hTyped := hNormal.parentPath_of_eventParentMap_ancestor hWidth hBound hColumn hPath.ancestor
  rw [Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth start column.isLt,
    Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth start parent.1.isLt] at hTyped
  refine ⟨hTyped, Frame.P_column_lt (build_normal_of_success hBuild).toOrdered hParent, ?_⟩
  intro z hRecord hBefore
  have hFront : Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start z.1 = z :=
    hNormal.parentPath_eventFrontier start rfl hRecord
  have hzBound : z.1.val ≤ bound := (hRecord.column_le (build_normal_of_success hBuild).toOrdered).trans hColumn
  have hMapRecord : z.1.val = column.val ∨
      Ancestor (Frame.eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound start) column.val z.1.val := by
    rcases hNormal.parentPath_eventParentMap hWidth rfl hColumn hRecord with hEq | ha
    · exact Or.inl (congrArg (fun u : (Frame.ofMountain mountain).Node => u.1.val) hEq.symm)
    · exact Or.inr ha
  have hBarrier := hPath.value_at
    (fun {_ _} _ hp => Frame.eventParentMap_leftward (build_normal_of_success hBuild).toOrdered hWidth hBound start hp)
    hColumn hMapRecord hBefore
  rw [Frame.eventValues_at (build_normal_of_success hBuild).toOrdered hWidth start z.1, hFront] at hBarrier
  exact ⟨hFront, hzBound, hBarrier⟩

/-- The strict typed projection also produces a concrete blocker when a
later parent column differs from the earlier immediate candidate column. -/
theorem build_event_parent_candidate_blocker
    {bound start event : Nat} (hBound : bound < mountain.size)
    (hOrder : start ≤ event) (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (column : Fin (Frame.ofMountain mountain).width) (hColumn : column.val ≤ bound) {parent candidate : (Frame.ofMountain mountain).Node}
    (hParent : (Frame.ofMountain mountain).P (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event column) = some parent)
    (hCandidate : (Frame.ofMountain mountain).P (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start column) = some candidate)
    (hDistinct : parent.1.val ≠ candidate.1.val) :
    Frame.ParentPath (Frame.ofMountain mountain) candidate (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start parent.1) ∧
      ∃ z : (Frame.ofMountain mountain).Node, Frame.ParentPath (Frame.ofMountain mountain) candidate z ∧
        (Frame.ofMountain mountain).P z = some (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start parent.1) ∧
        Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start z.1 = z ∧ z.1.val ≤ bound ∧
        (Frame.ofMountain mountain).value (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event column) ≤ (Frame.ofMountain mountain).value z := by
  have hNormal := build_normal_of_success hBuild
  have hPath := build_event_parent_map_projection hBuild hWidth hBound hOrder hEvent column hColumn hParent
  have hCandidateFront : Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start candidate.1 = candidate :=
    hNormal.eventFrontier_parent start column hCandidate
  have hCandidateBound : candidate.1.val ≤ bound :=
    (Frame.P_column_lt (build_normal_of_success hBuild).toOrdered hCandidate).le.trans hColumn
  have hCandidateMap : Frame.eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound start column.val =
      some candidate.1.val := by
    rw [hNormal.eventParentMap_at hWidth start column hColumn, hCandidate]
    rfl
  have hCandidatePath : Ancestor (Frame.eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound start)
      candidate.1.val parent.1.val := by
    rcases ancestor_eq_or_below_parent hCandidateMap hPath.ancestor with he | ha
    · exact (hDistinct he).elim
    · exact ha
  have hTyped := hNormal.parentPath_of_eventParentMap_ancestor hWidth hBound
    hCandidateBound hCandidatePath
  rw [Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth start candidate.1.isLt, hCandidateFront,
    Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth start parent.1.isLt] at hTyped
  obtain ⟨z, hZ, hLast, hBarrier⟩ := hPath.exists_last_edge
  have hZCandidate : z = candidate.1.val ∨
      Ancestor (Frame.eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound start) candidate.1.val z := by
    rcases hZ with rfl | ha
    · exact (hDistinct (Option.some.inj (hLast.symm.trans hCandidateMap))).elim
    · exact ancestor_eq_or_below_parent hCandidateMap ha
  have hZBound : z ≤ bound := by
    rcases hZCandidate with rfl | ha
    · exact hCandidateBound
    · exact (ancestor_lt (Frame.eventParentMap_leftward (build_normal_of_success hBuild).toOrdered hWidth hBound start) ha).le.trans
        hCandidateBound
  let zNode := Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start ⟨z, hZBound.trans_lt hBound⟩
  have hZTyped : Frame.ParentPath (Frame.ofMountain mountain) candidate zNode := by
    rcases hZCandidate with he | ha
    · have hzEq : (⟨z, hZBound.trans_lt hBound⟩ : Fin (Frame.ofMountain mountain).width) = candidate.1 := Fin.ext he
      simpa only [zNode, hzEq, hCandidateFront] using (Frame.ParentPath.refl candidate)
    · have h := hNormal.parentPath_of_eventParentMap_ancestor hWidth hBound hCandidateBound ha
      rw [Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth start candidate.1.isLt, hCandidateFront,
        Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth start (hZBound.trans_lt hBound)] at h
      exact h
  have hLastTyped := hNormal.eventParentMap_some hWidth hBound hZBound hLast
  rw [Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth start (hZBound.trans_lt hBound),
    Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth start parent.1.isLt] at hLastTyped
  have hZValue : Frame.eventValues (build_normal_of_success hBuild).toOrdered hWidth start z = (Frame.ofMountain mountain).value zNode :=
    Frame.eventValues_at (build_normal_of_success hBuild).toOrdered hWidth start ⟨z, hZBound.trans_lt hBound⟩
  rw [hZValue] at hBarrier
  exact ⟨hTyped, zNode, hZTyped, hLastTyped, rfl, hZBound, hBarrier⟩

end Built

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.eventParentMap_some
#print axioms OmegaY.Geometry.Frame.Normal.parentPath_of_eventParentMap_ancestor
#print axioms OmegaY.Expansion.build_event_parent_map_projection
#print axioms OmegaY.Expansion.build_event_parent_projection
#print axioms OmegaY.Expansion.build_event_parent_candidate_blocker
