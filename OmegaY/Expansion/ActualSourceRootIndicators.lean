/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/ActualSourceRootIndicators.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CommonRootIndicators
import OmegaY.Expansion.RawNumericSuffix

/-!
# Source root indicators from one actual common frontier parent

`CommonRootIndicators` already proves the nearest-smaller coefficient facts
for actual successful source builds. This module supplies their missing
source interface: a genuine common numerical parent at event `previous`
gives a common candidate map at `previous + 1`. Equal event depths propagate
that candidate equality up to the first different event.

Thus coefficient equality/ordering are conclusions of the actual source
parent equations and numerical recovery. They are not inferred from depths
in an arbitrary forest. In the formulas below `eventParentMap event` is the
designated map and equals `canonicalForests (event + 1)`; there is no extra
shift of the displayed depth or root indicator.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- Actual source P equality supplies the next event's common candidate
forest. Neither a guessed candidate chain nor a new parent is supplied. -/
theorem build_common_frontier_candidate_parent
    {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound previous : Nat}
    (left right : Fin (Frame.ofMountain mountain).width)
    (hLeft : left.val ≤ bound) (hRight : right.val ≤ bound)
    (hCommon : (Frame.ofMountain mountain).P
        (eventFrontier (build_normal_of_success hBuild).toOrdered previous left) =
      (Frame.ofMountain mountain).P
        (eventFrontier (build_normal_of_success hBuild).toOrdered previous right)) :
    canonicalForests hBuild hWidth bound (previous + 1) left.val =
      canonicalForests hBuild hWidth bound (previous + 1) right.val := by
  change eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound previous left.val =
    eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound previous right.val
  rw [(build_normal_of_success hBuild).eventParentMap_at hWidth previous left hLeft,
    (build_normal_of_success hBuild).eventParentMap_at hWidth previous right hRight, hCommon]

private theorem source_forests_leftward {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound : Nat} (hBound : bound < mountain.size) (event : Nat) :
    Leftward (canonicalForests hBuild hWidth bound event) := by
  apply Frame.frontierForests_leftward (build_normal_of_success hBuild).toOrdered
    (Frame.bottomCandidateMap_leftward bound)
  intro r c hc
  rw [Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth r
    (hc.trans_lt hBound)]
  rfl

/-- Source numeric recovery carries one common candidate equality through
every earlier equal depth, so it is still available at the first difference.
No per-event common-parent invariant is assumed. -/
theorem build_candidate_parent_at_first_difference
    {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound start event left right : Nat} (hBound : bound < mountain.size)
    (hLeft : left ≤ bound) (hRight : right ≤ bound)
    (hInitial : canonicalForests hBuild hWidth bound start left =
      canonicalForests hBuild hWidth bound start right)
    (hStart : start ≤ event) (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (hEarlier : ∀ r, start ≤ r → r < event →
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound r) left =
        parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound r) right) :
    canonicalForests hBuild hWidth bound event left =
      canonicalForests hBuild hWidth bound event right := by
  have hNumeric := build_eventFrontier_numeric_full hBuild hWidth hBound
  induction event with
  | zero =>
      have hZero : start = 0 := by omega
      simpa only [hZero] using hInitial
  | succ event ih =>
      by_cases hAtStart : start = event + 1
      · simpa only [hAtStart] using hInitial
      · have hBefore : start ≤ event := by omega
        have hEventBound : event ≤ (Frame.ofMountain mountain).lastEvent := by omega
        have hCommon := ih hBefore hEventBound (fun r hr hre => hEarlier r hr (by omega))
        exact Forests.event_parent_eq_of_depth_eq (source_forests_leftward hBuild hWidth hBound event)
          hNumeric (Nat.zero_le _) hEventBound hLeft hRight hCommon
          (hEarlier event hBefore (Nat.lt_succ_self _))

section ActualSource

variable {input : List Nat} {mountain : Mountain}
  (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
  {bound previous event : Nat} (hBound : bound < mountain.size)
  (left right : Fin (Frame.ofMountain mountain).width)
  (hLeft : left.val ≤ bound) (hRight : right.val ≤ bound)
  (hCommon : (Frame.ofMountain mountain).P
      (eventFrontier (build_normal_of_success hBuild).toOrdered previous left) =
    (Frame.ofMountain mountain).P
      (eventFrontier (build_normal_of_success hBuild).toOrdered previous right))
  (hStart : previous + 1 ≤ event) (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
  (hEarlier : ∀ r, previous + 1 ≤ r → r < event →
    parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound r) left.val =
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound r) right.val)

include hBound hLeft hRight hCommon hStart hEvent hEarlier

private theorem actual_source_common_at_difference :
    canonicalForests hBuild hWidth bound event left.val =
      canonicalForests hBuild hWidth bound event right.val :=
  build_candidate_parent_at_first_difference hBuild hWidth hBound hLeft hRight
    (build_common_frontier_candidate_parent hBuild hWidth left right hLeft hRight hCommon)
    hStart hEvent hEarlier

/-- The actual designated ancestor sets are nested in the depth order.
The source's common candidate condition is recovered from the one previous
typed parent equality and all intervening equal depths. -/
theorem build_source_root_ancestor_at_first_difference {root : Nat}
    (hDepth : parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val ≤
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val)
    (hAncestor : Ancestor (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event)
      left.val root) :
    Ancestor (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val root :=
  build_event_root_ancestor_mono hBuild hWidth hBound hEvent hLeft hRight
    (actual_source_common_at_difference hBuild hWidth hBound left right hLeft hRight hCommon hStart hEvent hEarlier)
    hDepth hAncestor

/-- The designated ancestor sets at the first difference are actually
nested. Their inclusion direction is determined by their finite depths. -/
theorem build_source_ancestor_sets_comparable :
    (∀ root, Ancestor (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val root →
      Ancestor (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val root) ∨
    (∀ root, Ancestor (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val root →
      Ancestor (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val root) := by
  rcases Nat.le_total
      (parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val)
      (parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val) with h | h
  · exact Or.inl (fun _ hAncestor => build_source_root_ancestor_at_first_difference hBuild hWidth hBound
      left right hLeft hRight hCommon hStart hEvent hEarlier h hAncestor)
  · exact Or.inr (fun _ hAncestor => build_source_root_ancestor_at_first_difference hBuild hWidth hBound
      right left hRight hLeft hCommon.symm hStart hEvent
        (fun r hr hre => (hEarlier r hr hre).symm) h hAncestor)

/-- Equal actual event depths give identical root coefficients. The root
may be any column; in particular this covers every root strictly to the left. -/
theorem build_source_rootIndicator_eq_at_first_difference (root : Nat)
    (hDepth : parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val =
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val) :
    Forests.rootIndicator (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) root left.val =
      Forests.rootIndicator (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) root right.val :=
  build_event_rootIndicator_eq hBuild hWidth hBound hEvent hLeft hRight
    (actual_source_common_at_difference hBuild hWidth hBound left right hLeft hRight hCommon hStart hEvent hEarlier)
    hDepth

/-- Weak depth order includes the strict first-difference case and forces
the coefficient of the left column to be at most that of the right. -/
theorem build_source_rootIndicator_le_at_first_difference (root : Nat)
    (hDepth : parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val ≤
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val) :
    Forests.rootIndicator (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) root left.val ≤
      Forests.rootIndicator (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) root right.val :=
  build_event_rootIndicator_le hBuild hWidth hBound hEvent hLeft hRight
    (actual_source_common_at_difference hBuild hWidth hBound left right hLeft hRight hCommon hStart hEvent hEarlier)
    hDepth

/-- Any shared nonnegative root correction preserves an earlier equal
event. No coefficient equality is assumed. -/
theorem build_source_corrected_depth_eq (root extra : Nat)
    (hDepth : parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val =
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val) :
    parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val +
        Forests.rootIndicator (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) root left.val * extra =
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val +
        Forests.rootIndicator (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) root right.val * extra :=
  build_event_compensated_depth_eq hBuild hWidth hBound hEvent hLeft hRight
    (actual_source_common_at_difference hBuild hWidth hBound left right hLeft hRight hCommon hStart hEvent hEarlier)
    hDepth extra

/-- At the first strict difference every common nonnegative root correction
keeps the strict direction. This remains a source-side implication: actual
two-column sharing of the correction and target cut is a separate task. -/
theorem build_source_corrected_depth_lt (root extra : Nat)
    (hDepth : parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val <
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val) :
    parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) left.val +
        Forests.rootIndicator (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) root left.val * extra <
      parentDepth (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) right.val +
        Forests.rootIndicator (eventParentMap (build_normal_of_success hBuild).toOrdered hWidth bound event) root right.val * extra :=
  build_event_compensated_depth_lt hBuild hWidth hBound hEvent hLeft hRight
    (actual_source_common_at_difference hBuild hWidth hBound left right hLeft hRight hCommon hStart hEvent hEarlier)
    hDepth extra

end ActualSource
end OmegaY.Expansion

#print axioms OmegaY.Expansion.build_common_frontier_candidate_parent
#print axioms OmegaY.Expansion.build_candidate_parent_at_first_difference
#print axioms OmegaY.Expansion.build_source_root_ancestor_at_first_difference
#print axioms OmegaY.Expansion.build_source_ancestor_sets_comparable
#print axioms OmegaY.Expansion.build_source_rootIndicator_eq_at_first_difference
#print axioms OmegaY.Expansion.build_source_rootIndicator_le_at_first_difference
#print axioms OmegaY.Expansion.build_source_corrected_depth_eq
#print axioms OmegaY.Expansion.build_source_corrected_depth_lt
