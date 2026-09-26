/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/InitialBoundaryFrontierPath.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.LowBoundaryRecordPath

/-!
# Initial lower-root references at every earlier actual frontier

The reduced mountain is itself a successful canonical build. Its actual
boundary reference below the root upper is an endpoint of a known raw path.
That path is first recognized in the reduced source, then projected to the
requested earlier finite event. A high reference is never assumed to be
the earlier frontier. No later copied-block reference is covered here.
-/

namespace OmegaY.Expansion

open Canonical Geometry ZeroY ZeroY.Forest

/-- Project a whole actual source-parent path from one actual event to an
earlier event. Each edge uses the existing canonical event projection; the
physical source path may cross many columns and heights. -/
theorem build_parent_path_event_projection {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {start event : Nat} (hOrder : start ≤ event)
    (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    {u p : (Frame.ofMountain mountain).Node}
    (hFront : Frame.eventFrontier (build_normal_of_success hBuild).toOrdered event u.1 = u)
    (path : Frame.ParentPath (Frame.ofMountain mountain) u p) :
    Frame.ParentPath (Frame.ofMountain mountain)
      (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start u.1)
      (Frame.eventFrontier (build_normal_of_success hBuild).toOrdered start p.1) := by
  have hNormal := build_normal_of_success hBuild
  have hBound : mountain.size - 1 < mountain.size := by omega
  induction path with
  | refl _ => exact .refl _
  | @cons u next p hParent tail ih =>
    have hAt : (Frame.ofMountain mountain).P
        (Frame.eventFrontier hNormal.toOrdered event u.1) = some next := by
      rw [hFront]
      exact hParent
    have hColumn : u.1.val ≤ mountain.size - 1 := Nat.le_sub_one_of_lt u.1.isLt
    have hProjected := (build_event_parent_projection hBuild hWidth hBound hOrder hEvent u.1 hColumn hAt).1
    have hNextFront := hNormal.eventFrontier_parent event u.1 hAt
    exact hProjected.trans (ih hNextFront)

private theorem parentPath_raw_refs {mountain : Mountain}
    (hNormal : (Frame.ofMountain mountain).Normal)
    {u p : (Frame.ofMountain mountain).Node}
    (path : Frame.ParentPath (Frame.ofMountain mountain) u p) :
    RawRefPath mountain (Frame.ref u) (Frame.ref p) := by
  induction path with
  | refl _ => exact .refl _
  | cons hParent _ ih =>
    have hReal := Frame.real_of_value_pos hNormal.toOrdered
      ((Frame.P_value hNormal.toOrdered hParent).1.trans (Frame.P_value hNormal.toOrdered hParent).2)
    exact .cons (RawRefEdge.of_rawParent ((hNormal.rawParent_eq_P hReal).trans hParent)) ih

private theorem upper_of_ref_successor {F : Frame} {lower upper : F.Node}
    (hRef : Frame.ref upper = ⟨lower.1.val, lower.2.val + 1⟩) :
    F.upper lower = some upper := by
  rcases lower with ⟨c, i⟩
  rcases upper with ⟨d, j⟩
  simp only [Frame.ref, Ref.mk.injEq] at hRef
  have hColumn : d = c := Fin.ext hRef.1
  subst d
  have hLength : i.val + 1 < F.length c := by have := j.isLt; omega
  simp only [Frame.upper, hLength, ↓reduceDIte, Option.some.injEq]
  apply Executable.ref_injective F
  simp only [Frame.ref, Ref.mk.injEq]
  exact ⟨trivial, hRef.2.symm⟩

/-- At any actual reduced event in a genuine lower root interval, the
last-column frontier reaches the unchanged original root. The resulting
frontier depth is strictly larger because these are different columns. -/
theorem Preparation.initial_low_root_frontier_path {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last)
    {root rootUpper : (Frame.ofMountain p.initial).Node}
    (hRootReal : Frame.Real root) (hRootColumn : root.1.val = p.root.column)
    (hBefore : root.2.val < p.root.index)
    (hRootUpper : (Frame.ofMountain p.initial).upper root = some rootUpper)
    (event : Nat)
    (hLow : (Frame.ofMountain p.initial).height root ≤ (Frame.ofMountain p.reduced).eventCut event)
    (hHigh : (Frame.ofMountain p.reduced).eventCut event < (Frame.ofMountain p.initial).height rootUpper) :
    let G := Frame.ofMountain p.reduced
    let hN := build_normal_of_success p.reduced_build
    let hWidth : 0 < p.reduced.size := (Nat.zero_le _).trans_lt p.reduced_last_exists
    let boundary : Fin G.width := ⟨p.reduced.size - 1, p.reduced_last_exists⟩
    ∃ reducedRoot : G.Node,
      Frame.ref reducedRoot = Frame.ref root ∧ G.cell reducedRoot = (Frame.ofMountain p.initial).cell root ∧
      Frame.eventFrontier hN.toOrdered event reducedRoot.1 = reducedRoot ∧
      Frame.ParentPath G (Frame.eventFrontier hN.toOrdered event boundary) reducedRoot ∧
      RawRefPath p.reduced (Frame.ref (Frame.eventFrontier hN.toOrdered event boundary)) (Frame.ref root) ∧
      parentDepth (Frame.eventParentMap hN.toOrdered hWidth (p.reduced.size - 1) event) reducedRoot.1.val <
        parentDepth (Frame.eventParentMap hN.toOrdered hWidth (p.reduced.size - 1) event) boundary.val := by
  let F := Frame.ofMountain p.initial
  let G := Frame.ofMountain p.reduced
  have hN : G.Normal := build_normal_of_success p.reduced_build
  have hWidth : 0 < p.reduced.size := (Nat.zero_le _).trans_lt p.reduced_last_exists
  let boundary : Fin G.width := ⟨p.reduced.size - 1, p.reduced_last_exists⟩
  change ∃ reducedRoot : G.Node,
    Frame.ref reducedRoot = Frame.ref root ∧ G.cell reducedRoot = F.cell root ∧
    Frame.eventFrontier hN.toOrdered event reducedRoot.1 = reducedRoot ∧
    Frame.ParentPath G (Frame.eventFrontier hN.toOrdered event boundary) reducedRoot ∧
    RawRefPath p.reduced (Frame.ref (Frame.eventFrontier hN.toOrdered event boundary)) (Frame.ref root) ∧
    parentDepth (Frame.eventParentMap hN.toOrdered hWidth (p.reduced.size - 1) event) reducedRoot.1.val <
      parentDepth (Frame.eventParentMap hN.toOrdered hWidth (p.reduced.size - 1) event) boundary.val
  have hRootLeft : root.1.val < front.length := hRootColumn ▸ p.root_before_last
  have hRootRead : Canonical.cellAt p.reduced (Frame.ref root) = .ok (F.cell root) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hRootLeft).symm.trans
      (Canonical.cellAt_of_frame_node p.initial root)
  have hUpperLeft : rootUpper.1.val < front.length := by
    rw [congrArg Fin.val (Frame.upper_spec hRootUpper).1]
    exact hRootLeft
  have hUpperRead : Canonical.cellAt p.reduced (Frame.ref rootUpper) = .ok (F.cell rootUpper) :=
    (build_changed_last_preserves_ref p.initial_build p.reduced_build hUpperLeft).symm.trans
      (Canonical.cellAt_of_frame_node p.initial rootUpper)
  obtain ⟨reducedRoot, hRootRef, hRootCell⟩ := Canonical.frame_node_of_cellAt hRootRead
  obtain ⟨reducedUpper, hUpperRef, hUpperCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
  have hRootHeight : G.height reducedRoot = F.height root := congrArg Cell.row hRootCell
  have hUpperHeight : G.height reducedUpper = F.height rootUpper := congrArg Cell.row hUpperCell
  have hUpper : G.upper reducedRoot = some reducedUpper := by
    apply upper_of_ref_successor
    rw [hUpperRef]
    simp only [Frame.ref, Ref.mk.injEq]
    constructor
    · exact (congrArg Fin.val (Frame.upper_spec hRootUpper).1).trans (congrArg Ref.column hRootRef).symm
    · exact (Frame.upper_spec hRootUpper).2.trans (congrArg (fun r : Ref => r.index + 1) hRootRef).symm
  obtain ⟨capEvent, hCapEvent, hCapCut⟩ := Frame.real_height_at_event hN.toOrdered (upper_real hUpper)
  have hEarlier : event < capEvent := by
    by_contra hn
    have hRows := G.eventCut_monotone (Nat.le_of_not_gt hn)
    rw [hCapCut, hUpperHeight] at hRows
    exact (not_lt_of_ge hRows) hHigh
  let prior := capEvent - 1
  have hPrior : prior < G.lastEvent := by dsimp only [prior]; omega
  have hNext : prior + 1 = capEvent := by dsimp only [prior]; omega
  have hOrder : event ≤ prior := by dsimp only [prior]; omega
  have hPriorCut : G.eventCut (prior + 1) = F.height rootUpper :=
    (congrArg G.eventCut hNext).trans (hCapCut.trans hUpperHeight)
  obtain ⟨reference, cell, hBelow, _, _, _, hRawPath⟩ :=
    p.initial_low_root_reference_path hLast hRootReal hRootColumn hBefore hRootUpper
  have hFrontBelow := eventFrontier_below_next_cut p.reduced_valid hPrior boundary
  change below p.reduced (p.reduced.size - 1) (G.eventCut (prior + 1)) =
    .ok (Frame.ref (Frame.eventFrontier hN.toOrdered prior boundary)) at hFrontBelow
  rw [hPriorCut] at hFrontBelow
  have hReference : Frame.ref (Frame.eventFrontier hN.toOrdered prior boundary) = reference :=
    Except.ok.inj (hFrontBelow.symm.trans hBelow)
  have hOldPath : Frame.ParentPath G (Frame.eventFrontier hN.toOrdered prior boundary) reducedRoot :=
    hRawPath.toParentPath hN.toOrdered (bound := p.reduced.size)
      (fun _ _ hReal => hN.rawParent_eq_P hReal) hReference hRootRef
      (Frame.eventFrontier_spec hN.toOrdered prior boundary).2.1 boundary.isLt
  have hProjected := build_parent_path_event_projection p.reduced_build hWidth hOrder hPrior.le rfl hOldPath
  rw [(Frame.eventFrontier_spec hN.toOrdered prior boundary).1] at hProjected
  have hRootFront : Frame.eventFrontier hN.toOrdered event reducedRoot.1 = reducedRoot := by
    apply Frame.frontierAt_eq_of_upper_barrier hN.toOrdered (G.eventCut_one_le event)
      (hRootHeight.trans_le hLow)
    intro upper hActual
    have he : upper = reducedUpper := Option.some.inj (hActual.symm.trans hUpper)
    exact hHigh.trans_eq (hUpperHeight.symm.trans (congrArg G.height he).symm)
  rw [hRootFront] at hProjected
  have hReducedRootColumn : reducedRoot.1.val = root.1.val := congrArg Ref.column hRootRef
  have hSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSize
  have hStrictColumn : reducedRoot.1.val < boundary.val := by
    change reducedRoot.1.val < p.reduced.size - 1
    omega
  have hMapPath := hN.parentPath_eventParentMap hWidth rfl (Nat.le_refl (p.reduced.size - 1)) hProjected
  have hDepth : parentDepth (Frame.eventParentMap hN.toOrdered hWidth (p.reduced.size - 1) event) reducedRoot.1.val <
      parentDepth (Frame.eventParentMap hN.toOrdered hWidth (p.reduced.size - 1) event) boundary.val := by
    rcases hMapPath with hEqual | hAncestor
    · have hc := congrArg (fun node : G.Node => node.1.val) hEqual
      rw [(Frame.eventFrontier_spec hN.toOrdered event boundary).1] at hc
      omega
    · exact ancestor_depth_lt
        (Frame.eventParentMap_leftward hN.toOrdered hWidth p.reduced_last_exists event) hAncestor
  exact ⟨reducedRoot, hRootRef, hRootCell, hRootFront, hProjected,
    by simpa only [hRootRef] using parentPath_raw_refs hN hProjected, hDepth⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_parent_path_event_projection
#print axioms OmegaY.Expansion.Preparation.initial_low_root_frontier_path
