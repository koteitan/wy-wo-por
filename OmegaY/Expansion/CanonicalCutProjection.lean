/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CanonicalCutProjection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CanonicalEventProjection
import OmegaY.Expansion.ContourCapBarrier

/-! Strict-cut projections of genuine source P edges. The cut is the actual
upper row of a real node in the parent's column, and the selected starting
reference is obtained from the executable strict-below search. -/

namespace OmegaY.Expansion

open Canonical Geometry

private theorem cut_upper_height_lt {F : Frame} (hF : F.Ordered) {u upper : F.Node}
    (hUpper : F.upper u = some upper) : F.height u < F.height upper := by
  rcases u with ⟨c, i⟩
  unfold Frame.upper at hUpper
  split at hUpper
  · obtain rfl := Option.some.inj hUpper
    exact hF.rows_strict c (show i.val < i.val + 1 by omega)
  · cases hUpper

theorem eventFrontier_below_next_cut {mountain : Mountain}
    (hValid : MountainValid mountain) {event : Nat}
    (hEvent : event < (Frame.ofMountain mountain).lastEvent)
    (column : Fin (Frame.ofMountain mountain).width) :
    below mountain column.val ((Frame.ofMountain mountain).eventCut (event + 1)) =
      .ok (Frame.ref (Frame.eventFrontier hValid.toOrdered event column)) := by
  let F := Frame.ofMountain mountain
  let chosen := Frame.eventFrontier hValid.toOrdered event column
  have hSpec := Frame.eventFrontier_spec hValid.toOrdered event column
  have hLow : F.height chosen < F.eventCut (event + 1) :=
    hSpec.2.2.1.trans_lt (F.eventCut_strict_step hEvent)
  apply below_eq_of_row_barrier (Array.getElem?_eq_getElem column.isLt)
    (hValid column.val column.isLt) (Array.getElem?_eq_getElem chosen.2.isLt) _ hLow le_rfl
  intro index other hOther hAbove
  by_contra hHigh
  obtain ⟨hi, hCell⟩ := Array.getElem?_eq_some_iff.mp hOther
  let node : F.Node := ⟨column, ⟨index, hi⟩⟩
  have hNodeRow : F.height node = other.row := congrArg Cell.row hCell
  have hPast : F.eventCut event < F.height node := by
    by_contra hNot
    have hIndex := hSpec.2.2.2.1 ⟨index, hi⟩ (le_of_not_gt hNot)
    have hRows := (hValid.toOrdered.rows_strict column).monotone hIndex
    change F.height node ≤ F.height chosen at hRows
    rw [hNodeRow] at hRows
    exact (not_lt_of_ge hRows) hAbove
  exact F.eventCut_no_between hEvent node hPast (by rw [hNodeRow]; exact lt_of_not_ge hHigh)

/-- A physical parent edge projects through every lower real interval in
the parent's column. The returned path consists of actual canonical P
edges, and its start is the actual executable boundary selector. -/
theorem build_parent_path_below_parent_upper {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain)
    {child parent root rootUpper : (Frame.ofMountain mountain).Node}
    (hParent : (Frame.ofMountain mountain).P child = some parent)
    (hRootReal : Frame.Real root) (hRootColumn : root.1 = parent.1)
    (hRootUpper : (Frame.ofMountain mountain).upper root = some rootUpper)
    (hCap : (Frame.ofMountain mountain).height rootUpper ≤
      (Frame.ofMountain mountain).height parent) :
    ∃ reference : (Frame.ofMountain mountain).Node,
      Frame.Real reference ∧ reference.1 = child.1 ∧
      below mountain child.1.val ((Frame.ofMountain mountain).height rootUpper) =
        .ok (Frame.ref reference) ∧
      (Frame.ofMountain mountain).height reference < (Frame.ofMountain mountain).height rootUpper ∧
      Frame.ParentPath (Frame.ofMountain mountain) reference root := by
  let F := Frame.ofMountain mountain
  have hNormal : F.Normal := build_normal_of_success hBuild
  have hValid := build_valid_of_success hBuild
  have hWidth : 0 < mountain.size := (Nat.zero_le child.1.val).trans_lt child.1.isLt
  have hChildReal : Frame.Real child :=
    Frame.real_of_value_pos hNormal.toOrdered
      ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
  have hRootLt : F.height root < F.height rootUpper :=
    cut_upper_height_lt hNormal.toOrdered hRootUpper
  have hCapOne : (1 : Row) < F.height rootUpper :=
    (Frame.one_le_height hNormal.toOrdered hRootReal).trans_lt hRootLt
  obtain ⟨capEvent, hCapEvent, hCapRow⟩ :=
    Frame.real_height_at_event hNormal.toOrdered (upper_real hRootUpper)
  change capEvent ≤ F.lastEvent at hCapEvent
  change F.eventCut capEvent = F.height rootUpper at hCapRow
  have hPositive : 0 < capEvent := by
    by_contra hn
    have he : capEvent = 0 := by omega
    rw [he, F.eventCut_zero] at hCapRow
    exact (lt_irrefl (1 : Row)) (by simpa only [← hCapRow] using hCapOne)
  let earlier := capEvent - 1
  have hEarlier : earlier < F.lastEvent := by dsimp only [earlier]; omega
  have hNext : earlier + 1 = capEvent := by dsimp only [earlier]; omega
  have hBelowCap : F.eventCut earlier < F.height rootUpper := by
    simpa only [hNext, hCapRow] using F.eventCut_strict_step hEarlier
  have hRootBefore : F.height root ≤ F.eventCut earlier := by
    by_contra hn
    exact F.eventCut_no_between hEarlier root (lt_of_not_ge hn)
      (by simpa only [hNext, hCapRow] using hRootLt)
  have hRootFront : Frame.eventFrontier hNormal.toOrdered earlier parent.1 = root := by
    rw [← hRootColumn]
    apply Frame.frontierAt_eq_of_upper_barrier hNormal.toOrdered (F.eventCut_one_le earlier)
      hRootBefore
    intro upper hUpper
    have he : upper = rootUpper := Option.some.inj (hUpper.symm.trans hRootUpper)
    exact he ▸ hBelowCap
  obtain ⟨event, hEvent, hRow⟩ := Frame.real_height_at_event hNormal.toOrdered hChildReal
  have hChildFront : Frame.eventFrontier hNormal.toOrdered event child.1 = child := by
    apply Frame.frontierAt_eq_of_upper_barrier hNormal.toOrdered (F.eventCut_one_le event)
      (le_of_eq hRow.symm)
    intro upper hUpper
    rw [hRow]
    exact cut_upper_height_lt hNormal.toOrdered hUpper
  have hOrder : earlier ≤ event := by
    by_contra hn
    have hRows := F.eventCut_monotone (Nat.le_of_lt (lt_of_not_ge hn))
    rw [hRow] at hRows
    exact (not_lt_of_ge ((hCap.trans (Frame.P_height_le hNormal.toOrdered hParent)).trans hRows))
      hBelowCap
  have hBound : mountain.size - 1 < mountain.size := by omega
  have hColumn : child.1.val ≤ mountain.size - 1 := by
    have hc : child.1.val < mountain.size := child.1.isLt
    omega
  have hProjected := (build_event_parent_projection hBuild hWidth hBound hOrder hEvent
    child.1 hColumn (by simpa only [hChildFront] using hParent)).1
  rw [hRootFront] at hProjected
  let reference := Frame.eventFrontier hNormal.toOrdered earlier child.1
  have hRefSpec := Frame.eventFrontier_spec hNormal.toOrdered earlier child.1
  refine ⟨reference, hRefSpec.2.1, hRefSpec.1, ?_, hRefSpec.2.2.1.trans_lt hBelowCap, hProjected⟩
  have hBelow := eventFrontier_below_next_cut hValid hEarlier child.1
  change below mountain child.1.val (F.eventCut (earlier + 1)) = .ok (Frame.ref reference) at hBelow
  rw [hNext, hCapRow] at hBelow
  exact hBelow

end OmegaY.Expansion

#print axioms OmegaY.Expansion.eventFrontier_below_next_cut
#print axioms OmegaY.Expansion.build_parent_path_below_parent_upper
