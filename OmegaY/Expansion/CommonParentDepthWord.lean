/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonParentDepthWord.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CanonicalFrontierInitial

/-!
# Actual common-parent nodes determine their upper event-depth suffix

The common candidate forest at the starting upper event is derived from
the actual preceding frontiers, rather than supplied as an independent
assumption. All numerical recovery here belongs to a successful source
build. This file does not transport source words into a copied mountain.
-/

namespace OmegaY.Geometry.Frame

private theorem upper_height_lt {F : Frame} (hF : F.Ordered) {u upper : F.Node}
    (hUpper : F.upper u = some upper) : F.height u < F.height upper := by
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    exact hF.rows_strict c (show i.val < i.val + 1 by omega)
  · cases hUpper

theorem Normal.common_parent_upper_rows {F : Frame} (hF : F.Normal)
    {u z parent uUpper zUpper : F.Node}
    (hUP : F.P u = some parent) (hZP : F.P z = some parent)
    (hUUpper : F.upper u = some uUpper) (hZUpper : F.upper z = some zUpper)
    (hOrder : F.height z ≤ F.height u) (hBefore : F.height u < F.height zUpper) :
    F.height uUpper = F.height zUpper := by
  have hURow := (aboveHeight_of_upper hUUpper).symm.trans (hF.above_row hUP)
  have hZRow := (aboveHeight_of_upper hZUpper).symm.trans (hF.above_row hZP)
  rw [hURow, hZRow]
  exact Row.B_eq_of_between hOrder (P_height_le hF.toOrdered hZP)
    (hBefore.trans_eq hZRow)

/-- At a genuine global event ending at an upper node, its preceding
frontier is the actual lower node. No normality or parent rule is used. -/
theorem eventFrontier_pair_of_upper_cut {F : Frame} (hF : F.Ordered)
    {u upper : F.Node} {event : Nat} (hEvent : event < F.lastEvent)
    (hUpper : F.upper u = some upper) (hCut : F.eventCut (event + 1) = F.height upper) :
    eventFrontier hF event u.1 = u ∧ eventFrontier hF (event + 1) u.1 = upper := by
  have hLower : F.height u < F.height upper := upper_height_lt hF hUpper
  have hBelow : F.height u ≤ F.eventCut event := by
    by_contra hn
    exact F.eventCut_no_between hEvent u (lt_of_not_ge hn) (hLower.trans_eq hCut.symm)
  have hBefore : F.eventCut event < F.height upper :=
    (F.eventCut_strict_step hEvent).trans_eq hCut
  constructor
  · apply frontierAt_eq_of_upper_barrier hF (F.eventCut_one_le event) hBelow
    intro actual hActual
    have he : actual = upper := Option.some.inj (hActual.symm.trans hUpper)
    exact he ▸ hBefore
  · have hAt : eventFrontier hF (event + 1) upper.1 = upper := by
      apply frontierAt_eq_of_upper_barrier hF (F.eventCut_one_le (event + 1)) hCut.ge
      intro next hNext
      exact hCut.trans_lt (upper_height_lt hF hNext)
    rw [← (upper_spec hUpper).1]
    exact hAt

/-- Every real adjacent pair occurs in consecutive actual frontier events;
other columns may have any number of earlier or later events. -/
theorem upper_at_positive_event {F : Frame} (hF : F.Ordered)
    {u upper : F.Node} (hReal : Real u) (hUpper : F.upper u = some upper) :
    ∃ event, event < F.lastEvent ∧ F.eventCut (event + 1) = F.height upper ∧
      eventFrontier hF event u.1 = u ∧ eventFrontier hF (event + 1) u.1 = upper := by
  have hOne : (1 : Row) < F.height upper :=
    (one_le_height hF hReal).trans_lt (upper_height_lt hF hUpper)
  obtain ⟨event, hEvent, hCut⟩ := eventCut_of_member
    (mem_eventCuts.mpr (height_mem_eventRows upper hOne.le))
  cases event with
  | zero =>
    rw [F.eventCut_zero] at hCut
    exact False.elim ((ne_of_lt hOne) hCut)
  | succ event =>
    have hLess : event < F.lastEvent := by omega
    exact ⟨event, hLess, hCut, eventFrontier_pair_of_upper_cut hF hLess hUpper hCut⟩

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry

/-- The source high-depth word starts at the common actual upper event.
Both previous frontier nodes and their common candidate parent are derived
from the source reads; only the common-parent source facts are inputs. -/
theorem build_common_parent_upper_depthWord {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound : Nat} (hBound : bound < mountain.size)
    {u z parent zUpper : (Frame.ofMountain mountain).Node}
    (hu : u.1.val ≤ bound) (hz : z.1.val ≤ bound)
    (hUP : (Frame.ofMountain mountain).P u = some parent)
    (hZP : (Frame.ofMountain mountain).P z = some parent)
    (hZUpper : (Frame.ofMountain mountain).upper z = some zUpper)
    (hOrder : (Frame.ofMountain mountain).height z ≤ (Frame.ofMountain mountain).height u)
    (hBefore : (Frame.ofMountain mountain).height u < (Frame.ofMountain mountain).height zUpper) :
    let F := Frame.ofMountain mountain
    let hN := build_normal_of_success hBuild
    let front := Frame.eventFrontierNat hN.toOrdered hWidth
    let forests := F.frontierForests (Frame.bottomCandidateMap bound) front bound
    ∃ uUpper event, F.upper u = some uUpper ∧ event < F.lastEvent ∧
      F.height uUpper = F.height zUpper ∧ F.eventCut (event + 1) = F.height uUpper ∧
      Frame.eventFrontier hN.toOrdered event u.1 = u ∧
      Frame.eventFrontier hN.toOrdered event z.1 = z ∧
      Frame.eventFrontier hN.toOrdered (event + 1) u.1 = uUpper ∧
      Frame.eventFrontier hN.toOrdered (event + 1) z.1 = zUpper ∧
      (Forests.DepthWordLe forests (event + 1) F.lastEvent u.1.val z.1.val ↔ F.value u ≤ F.value z) := by
  let F := Frame.ofMountain mountain
  have hN : F.Normal := build_normal_of_success hBuild
  let front := Frame.eventFrontierNat hN.toOrdered hWidth
  let forests := F.frontierForests (Frame.bottomCandidateMap bound) front bound
  change ∃ uUpper event, F.upper u = some uUpper ∧ event < F.lastEvent ∧
      F.height uUpper = F.height zUpper ∧ F.eventCut (event + 1) = F.height uUpper ∧
      Frame.eventFrontier hN.toOrdered event u.1 = u ∧
      Frame.eventFrontier hN.toOrdered event z.1 = z ∧
      Frame.eventFrontier hN.toOrdered (event + 1) u.1 = uUpper ∧
      Frame.eventFrontier hN.toOrdered (event + 1) z.1 = zUpper ∧
      (Forests.DepthWordLe forests (event + 1) F.lastEvent u.1.val z.1.val ↔ F.value u ≤ F.value z)
  have hUValues := Frame.P_value hN.toOrdered hUP
  have hZValues := Frame.P_value hN.toOrdered hZP
  have hUReal := Frame.real_of_value_pos hN.toOrdered (hUValues.1.trans hUValues.2)
  have hZReal := Frame.real_of_value_pos hN.toOrdered (hZValues.1.trans hZValues.2)
  obtain ⟨uUpper, hUUpper⟩ := hN.upper_of_parent hUP
  have hRows := hN.common_parent_upper_rows hUP hZP hUUpper hZUpper hOrder hBefore
  obtain ⟨event, hEvent, hCut, hUFront, hUFrontNext⟩ :=
    Frame.upper_at_positive_event hN.toOrdered hUReal hUUpper
  obtain ⟨hZFront, hZFrontNext⟩ :=
    Frame.eventFrontier_pair_of_upper_cut hN.toOrdered hEvent hZUpper (hCut.trans hRows)
  have hCommon : forests (event + 1) u.1.val = forests (event + 1) z.1.val := by
    change Frame.eventParentMap hN.toOrdered hWidth bound event u.1.val =
      Frame.eventParentMap hN.toOrdered hWidth bound event z.1.val
    rw [hN.eventParentMap_at hWidth event u.1 hu, hN.eventParentMap_at hWidth event z.1 hz,
      hUFront, hZFront, hUP, hZP]
  have hCompare := (build_eventDepth_value_comparison hBuild hWidth hBound
    (event + 1) u.1.val z.1.val (Nat.succ_le_of_lt hEvent) hu hz hCommon).2.2
  have hUValue : F.frontierValue front (event + 1) u.1.val = F.value uUpper := by
    dsimp only [Frame.frontierValue, front]
    rw [Frame.eventFrontierNat_eq hN.toOrdered hWidth _ u.1.isLt, hUFrontNext]
  have hZValue : F.frontierValue front (event + 1) z.1.val = F.value zUpper := by
    dsimp only [Frame.frontierValue, front]
    rw [Frame.eventFrontierNat_eq hN.toOrdered hWidth _ z.1.isLt, hZFrontNext]
  have hUSum : F.value u = F.value uUpper + F.value parent := by
    obtain ⟨actual, hActual, _, hValue, _⟩ := hN.upper_step u uUpper hUReal hUUpper
    have he : actual = parent := Option.some.inj (hActual.symm.trans hUP)
    subst actual
    omega
  have hZSum : F.value z = F.value zUpper + F.value parent := by
    obtain ⟨actual, hActual, _, hValue, _⟩ := hN.upper_step z zUpper hZReal hZUpper
    have he : actual = parent := Option.some.inj (hActual.symm.trans hZP)
    subst actual
    omega
  refine ⟨uUpper, event, hUUpper, hEvent, hRows, hCut, hUFront, hZFront,
    hUFrontNext, hZFrontNext, ?_⟩
  change Forests.DepthWordLe forests (event + 1) F.lastEvent u.1.val z.1.val ↔
    F.frontierValue front (event + 1) u.1.val ≤ F.frontierValue front (event + 1) z.1.val at hCompare
  rw [hUValue, hZValue] at hCompare
  exact hCompare.trans ((Frame.common_parent_backfill_le_iff hUSum hZSum).symm)

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.Normal.common_parent_upper_rows
#print axioms OmegaY.Geometry.Frame.eventFrontier_pair_of_upper_cut
#print axioms OmegaY.Geometry.Frame.upper_at_positive_event
#print axioms OmegaY.Expansion.build_common_parent_upper_depthWord
