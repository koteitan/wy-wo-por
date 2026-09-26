/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualMixedMarkerFrontier.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.ActualMixedMarkerSource
import OmegaY.Expansion.ActualLowEffectiveCandidate

/-!
# Actual shared frontiers for a mixed marker candidate pair

Two real source frontiers with one row and one geometric candidate may
already have different numerical parents. If exactly one is marked, the
other's effective row stays fixed. When it has an upper, its fixed-parent
record suffix places that source upper beyond the actual marked root cap;
its executed upper stays at this source height. A source top remains an
actual output top. Hence the marked effective target is a common cut.

No output numerical P, copied frontier, or target upper barrier is input.
The previous-event argument yielding the common source row and Q is separate.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame

namespace EffectiveCopyOccurrence

variable {front : List Nat} {last : Nat} {p : Preparation front last}
  {block : Nat} {start result : Mountain} {references : List Ref}
  {u z : (Frame.ofMountain p.reduced).Node}
  (uCopy : EffectiveCopyOccurrence p block start references u result)
  (zCopy : EffectiveCopyOccurrence p block start references z result)

theorem shared_contour_frontier_mixed_candidate (hLast : 1 < last) (hValid : MountainValid result)
    (hUMarked : BucketMem p.marked u.1.val (Frame.ref u))
    (hZUnmarked : z.2.val ∉ (p.marked[z.1.val]?.getD []).map Ref.index)
    (hSameRow : (Frame.ofMountain p.reduced).height u = (Frame.ofMountain p.reduced).height z)
    {candidate : (Frame.ofMountain p.reduced).Node}
    (hUQ : (Frame.ofMountain p.reduced).Q u = some candidate)
    (hZQ : (Frame.ofMountain p.reduced).Q z = some candidate)
    {cut : Row} (hCut : (1 : Row) ≤ cut)
    (hUFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut u.1 = u)
    (hZFront : frontierAt (build_normal_of_success p.reduced_build).toOrdered cut hCut z.1 = z) :
    Nonempty (SharedContourFrontier uCopy zCopy cut hValid) := by
  let F := Frame.ofMountain p.reduced
  let G := Frame.ofMountain result
  have hNormal := build_normal_of_success p.reduced_build
  have hUReal : Real u := hUFront ▸ (frontierAt_spec hNormal.toOrdered hCut u.1).2.1
  have hZReal : Real z := hZFront ▸ (frontierAt_spec hNormal.toOrdered hCut z.1).2.1
  have hUCut := uCopy.marked_frontier_cut_eq hUMarked hCut hUFront
  have hZCut : cut = F.height z := hUCut.trans hSameRow
  obtain ⟨rootIndex, a⟩ := uCopy.state.actual_marker_root_interval hLast hUMarked
    (Canonical.cellAt_of_frame_node p.reduced u)
    (Row.zero_lt_one.trans_le (one_le_height hNormal.toOrdered hUReal))
  obtain ⟨a⟩ := a
  have hTargetRow : a.target.row = uCopy.read.outputCell.row :=
    Except.ok.inj (a.ambient_query.symm.trans (uCopy.read.marked_reference hUMarked))
  have hUOwnRow : uCopy.contourCut cut = uCopy.read.outputCell.row := by
    rw [hUCut]
    exact uCopy.read.output_row.symm
  have hStationary := zCopy.stationary_at_marker_row hLast hZUnmarked hUMarked hSameRow.symm
  have hZOwnRow : zCopy.contourCut cut = cut := by
    calc
      zCopy.contourCut cut = zCopy.read.outputCell.row := by
        rw [hZCut]
        exact zCopy.read.output_row.symm
      _ = F.height z := hStationary
      _ = cut := hZCut.symm
  have hZNotMarked : ¬ BucketMem p.marked z.1.val (Frame.ref z) := by
    intro hm
    exact hZUnmarked (List.mem_map.mpr ⟨Frame.ref z, hm, rfl⟩)
  have hLiftOrder : zCopy.contourCut cut ≤ uCopy.contourCut cut := by
    rw [hZOwnRow, hUOwnRow, ← hTargetRow, hUCut]
    exact a.target_lower
  have hMax : max (uCopy.contourCut cut) (zCopy.contourCut cut) = uCopy.contourCut cut :=
    max_eq_left hLiftOrder
  obtain ⟨hUCutOne, uNode, hURef, hUCell, hUOwn⟩ :=
    uCopy.frontierAt_own_lift_of_marked hValid hUMarked hCut hUFront
  obtain ⟨hZCutOne, zNode, hZRef, hZCell, hZOwn⟩ :=
    zCopy.frontierAt_own_lift hLast hValid hZUnmarked hCut hZFront
  have hShared : (1 : Row) ≤ max (uCopy.contourCut cut) (zCopy.contourCut cut) :=
    hUCutOne.trans (le_max_left _ _)
  have hUShared : frontierAt hValid.toOrdered (max (uCopy.contourCut cut) (zCopy.contourCut cut))
      hShared uNode.1 = uNode := by simpa only [hMax] using hUOwn
  have hZShared : frontierAt hValid.toOrdered (max (uCopy.contourCut cut) (zCopy.contourCut cut))
      hShared zNode.1 = zNode := by
    apply frontierAt_eq_of_upper_barrier hValid.toOrdered hShared
    · have hLower : G.height zNode = F.height u := by
        change (G.cell zNode).row = F.height u
        rw [hZCell, hStationary, hSameRow]
      rw [hMax, hUOwnRow, ← hTargetRow, hLower]
      exact a.target_lower
    · intro targetUpper hTargetUpper
      cases hUpper : F.upper z with
      | none =>
        have hNone := zCopy.top_upper_none hLast hUpper hZRef
        rw [hNone] at hTargetUpper
        cases hTargetUpper
      | some sourceUpper =>
        obtain ⟨parent, hParent, hSourceB, _, _⟩ := hNormal.upper_step z sourceUpper hZReal hUpper
        have hSourceCap := a.cap_le_mixed_upper hUMarked hZNotMarked
          uCopy.state.next_lower zCopy.state.next_lower rfl hSameRow.symm hUQ hZQ hParent hUpper
        have hLowerLift : zCopy.read.outputCell.row = Row.lift (F.height z) (F.height z) (F.height z) :=
          hStationary.trans (Row.lift_identity le_rfl).symm
        obtain ⟨upperCell, hUpperRead, hUpperRow⟩ := zCopy.upper_read_of_lower_lift
          hLast hZUnmarked hParent hUpper le_rfl hLowerLift
        have hAbove : F.height z ≤ F.height sourceUpper := by
          rw [hSourceB]
          exact (Row.lt_B _ _).le
        rw [Row.lift_identity hAbove] at hUpperRow
        obtain ⟨actualUpper, hActualRef, hActualCell⟩ := Canonical.frame_node_of_cellAt hUpperRead
        have hEq : actualUpper = targetUpper := Option.some.inj
          ((Frame.upper_of_refs hZRef hActualRef).symm.trans hTargetUpper)
        have hTargetHeight : G.height targetUpper = F.height sourceUpper := by
          rw [← hEq]
          change (G.cell actualUpper).row = F.height sourceUpper
          rw [hActualCell]
          exact hUpperRow
        rw [hMax, hUOwnRow, ← hTargetRow, hTargetHeight]
        exact a.target_below.trans_le hSourceCap
  obtain ⟨event, hEvent, hBelow, hMaximal, hFrontiers⟩ := event_floor_at_cut hValid.toOrdered hShared
  exact ⟨⟨hUCutOne, hZCutOne, hShared, uNode, zNode, hURef, hZRef, hUCell, hZCell,
    hUOwn, hZOwn, hUShared, hZShared, event, hEvent, hBelow, hMaximal, hFrontiers⟩⟩

end EffectiveCopyOccurrence
end OmegaY.Expansion

#print axioms OmegaY.Expansion.EffectiveCopyOccurrence.shared_contour_frontier_mixed_candidate
