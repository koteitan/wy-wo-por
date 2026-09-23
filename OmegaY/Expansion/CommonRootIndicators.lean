/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonRootIndicators.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: `YesMetaZFC.BMS.transGen_head` is replaced by the lemma `Por.BMS.transGen_head` of this repository, which has the same statement.
-/
import OmegaY.Expansion.CanonicalFrontierInitial

/-!
# Actual source-event root indicators

The coefficient is one precisely when the specified root column is an
actual strict ancestor in the event's raw-parent forest. Successful source
construction supplies numerical recovery; coefficient comparisons are
conclusions, not additional assumptions.
-/

namespace OmegaY.Forests

open ZeroY ZeroY.Forest

noncomputable def rootIndicator (parent : ParentMap) (root column : Nat) : Nat := by
  classical
  exact if Ancestor parent column root then 1 else 0

theorem rootIndicator_zero_or_one (parent : ParentMap) (root column : Nat) :
    rootIndicator parent root column = 0 ∨ rootIndicator parent root column = 1 := by
  classical
  unfold rootIndicator
  split <;> simp

theorem rootIndicator_le_of_ancestor_imp {parent : ParentMap} {root left right : Nat}
    (h : Ancestor parent left root → Ancestor parent right root) :
    rootIndicator parent root left ≤ rootIndicator parent root right := by
  classical
  unfold rootIndicator
  split <;> split <;> simp_all

end OmegaY.Forests

namespace OmegaY.Expansion

open Canonical Geometry ZeroY ZeroY.Forest

/-- The actual bounded frontier forests of a successful source build.
The initial map is the genuine bottom predecessor map, including event zero. -/
noncomputable def canonicalForests {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    (bound : Nat) : Nat → ParentMap :=
  (Frame.ofMountain mountain).frontierForests (Frame.bottomCandidateMap bound)
    (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth) bound

private theorem canonicalForests_leftward {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound : Nat} (hBound : bound < mountain.size) (event : Nat) :
    Leftward (canonicalForests hBuild hWidth bound event) := by
  apply Frame.frontierForests_leftward (build_normal_of_success hBuild).toOrdered
    (Frame.bottomCandidateMap_leftward bound)
  intro r c hc
  rw [Frame.eventFrontierNat_eq (build_normal_of_success hBuild).toOrdered hWidth r
    (hc.trans_lt hBound)]
  rfl

/-- Source numeric recovery is an equality of the actual bounded maps.
Outside the selected prefix both maps are parentless, so no arbitrary
out-of-range value or clamped frontier is used as a parent. -/
theorem build_event_numeric_map_eq {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound event : Nat} (hBound : bound < mountain.size)
    (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent) :
    nearestSmaller (canonicalForests hBuild hWidth bound event)
      ((Frame.ofMountain mountain).frontierValue
        (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth) event) =
      canonicalForests hBuild hWidth bound (event + 1) := by
  funext column
  by_cases hc : column ≤ bound
  · exact build_eventFrontier_numeric_full hBuild hWidth hBound event (Nat.zero_le _) hEvent column hc
  · have hOld : canonicalForests hBuild hWidth bound event column = none := by
      cases event <;> simp only [canonicalForests, Frame.frontierForests,
        Frame.bottomCandidateMap, Frame.frontierParent, if_neg hc]
    have hNew : canonicalForests hBuild hWidth bound (event + 1) column = none := by
      simp only [canonicalForests, Frame.frontierForests, Frame.frontierParent, if_neg hc]
    rw [hNew]
    apply (nearestSmaller_none_iff (parent := canonicalForests hBuild hWidth bound event)
      (canonicalForests_leftward hBuild hWidth hBound event)).mpr
    intro candidate hAncestor
    rcases Por.BMS.transGen_head hAncestor with hEdge | ⟨_, hEdge, _⟩
    · rw [hOld] at hEdge
      cases hEdge
    · rw [hOld] at hEdge
      cases hEdge

/-- Shared actual candidate parents and ordered actual event depths force
inclusion of every root ancestor in the newly designated forest. -/
theorem build_event_root_ancestor_mono {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound event left right root : Nat} (hBound : bound < mountain.size)
    (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (hLeft : left ≤ bound) (hRight : right ≤ bound)
    (hCommon : canonicalForests hBuild hWidth bound event left =
      canonicalForests hBuild hWidth bound event right)
    (hDepth : Forests.eventDepth (canonicalForests hBuild hWidth bound) event left ≤
      Forests.eventDepth (canonicalForests hBuild hWidth bound) event right)
    (hAncestor : Ancestor (canonicalForests hBuild hWidth bound (event + 1)) left root) :
    Ancestor (canonicalForests hBuild hWidth bound (event + 1)) right root := by
  let forests := canonicalForests hBuild hWidth bound
  let values := (Frame.ofMountain mountain).frontierValue
    (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth)
  have hNumeric : Forests.NumericSuffix forests values bound 0 (Frame.ofMountain mountain).lastEvent :=
    build_eventFrontier_numeric_full hBuild hWidth hBound
  rcases Nat.eq_or_lt_of_le hDepth with hEq | hLt
  · have hParents := Forests.event_parent_eq_of_depth_eq
      (canonicalForests_leftward hBuild hWidth hBound event) hNumeric (Nat.zero_le _) hEvent
      hLeft hRight hCommon hEq
    exact (ancestor_iff_of_parent_eq hParents root).mp hAncestor
  · have hValues := Forests.event_value_lt_of_depth_lt
      (canonicalForests_leftward hBuild hWidth hBound event) hNumeric (Nat.zero_le _) hEvent
      hLeft hRight hCommon hLt
    have hMap := build_event_numeric_map_eq hBuild hWidth hBound hEvent
    have hOldAncestor : Ancestor (nearestSmaller (forests event) (values event)) left root := by
      rw [hMap]
      exact hAncestor
    have hNewAncestor := nearestSmaller_ancestor_mono
      (canonicalForests_leftward hBuild hWidth hBound event)
      (ancestor_iff_of_parent_eq hCommon) hValues.le hOldAncestor
    rw [hMap] at hNewAncestor
    exact hNewAncestor

theorem build_event_rootIndicator_le {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound event left right root : Nat} (hBound : bound < mountain.size)
    (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (hLeft : left ≤ bound) (hRight : right ≤ bound)
    (hCommon : canonicalForests hBuild hWidth bound event left =
      canonicalForests hBuild hWidth bound event right)
    (hDepth : Forests.eventDepth (canonicalForests hBuild hWidth bound) event left ≤
      Forests.eventDepth (canonicalForests hBuild hWidth bound) event right) :
    Forests.rootIndicator (canonicalForests hBuild hWidth bound (event + 1)) root left ≤
      Forests.rootIndicator (canonicalForests hBuild hWidth bound (event + 1)) root right :=
  Forests.rootIndicator_le_of_ancestor_imp
    (build_event_root_ancestor_mono hBuild hWidth hBound hEvent hLeft hRight hCommon hDepth)

theorem build_event_rootIndicator_eq {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound event left right root : Nat} (hBound : bound < mountain.size)
    (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (hLeft : left ≤ bound) (hRight : right ≤ bound)
    (hCommon : canonicalForests hBuild hWidth bound event left =
      canonicalForests hBuild hWidth bound event right)
    (hDepth : Forests.eventDepth (canonicalForests hBuild hWidth bound) event left =
      Forests.eventDepth (canonicalForests hBuild hWidth bound) event right) :
    Forests.rootIndicator (canonicalForests hBuild hWidth bound (event + 1)) root left =
      Forests.rootIndicator (canonicalForests hBuild hWidth bound (event + 1)) root right :=
  Nat.le_antisymm
    (build_event_rootIndicator_le hBuild hWidth hBound hEvent hLeft hRight hCommon hDepth.le)
    (build_event_rootIndicator_le hBuild hWidth hBound hEvent hRight hLeft hCommon.symm hDepth.ge)

/-- Any shared nonnegative compensation preserves an equal source event. -/
theorem build_event_compensated_depth_eq {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound event left right root : Nat} (hBound : bound < mountain.size)
    (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (hLeft : left ≤ bound) (hRight : right ≤ bound)
    (hCommon : canonicalForests hBuild hWidth bound event left =
      canonicalForests hBuild hWidth bound event right)
    (hDepth : Forests.eventDepth (canonicalForests hBuild hWidth bound) event left =
      Forests.eventDepth (canonicalForests hBuild hWidth bound) event right) :
    ∀ extra : Nat,
      Forests.eventDepth (canonicalForests hBuild hWidth bound) event left +
          Forests.rootIndicator (canonicalForests hBuild hWidth bound (event + 1)) root left * extra =
        Forests.eventDepth (canonicalForests hBuild hWidth bound) event right +
          Forests.rootIndicator (canonicalForests hBuild hWidth bound (event + 1)) root right * extra := by
  intro extra
  rw [hDepth, build_event_rootIndicator_eq hBuild hWidth hBound hEvent hLeft hRight hCommon hDepth]

/-- At a strict first difference the larger source depth keeps every root
ancestor of the smaller one, so every common compensation preserves strictness. -/
theorem build_event_compensated_depth_lt {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound event left right root : Nat} (hBound : bound < mountain.size)
    (hEvent : event ≤ (Frame.ofMountain mountain).lastEvent)
    (hLeft : left ≤ bound) (hRight : right ≤ bound)
    (hCommon : canonicalForests hBuild hWidth bound event left =
      canonicalForests hBuild hWidth bound event right)
    (hDepth : Forests.eventDepth (canonicalForests hBuild hWidth bound) event left <
      Forests.eventDepth (canonicalForests hBuild hWidth bound) event right) :
    ∀ extra : Nat,
      Forests.eventDepth (canonicalForests hBuild hWidth bound) event left +
          Forests.rootIndicator (canonicalForests hBuild hWidth bound (event + 1)) root left * extra <
        Forests.eventDepth (canonicalForests hBuild hWidth bound) event right +
          Forests.rootIndicator (canonicalForests hBuild hWidth bound (event + 1)) root right * extra := by
  intro extra
  have hCoefficient := build_event_rootIndicator_le (root := root) hBuild hWidth hBound hEvent
    hLeft hRight hCommon hDepth.le
  have hProduct := Nat.mul_le_mul_right extra hCoefficient
  omega

end OmegaY.Expansion

#print axioms OmegaY.Forests.rootIndicator_zero_or_one
#print axioms OmegaY.Forests.rootIndicator_le_of_ancestor_imp
#print axioms OmegaY.Expansion.build_event_numeric_map_eq
#print axioms OmegaY.Expansion.build_event_root_ancestor_mono
#print axioms OmegaY.Expansion.build_event_rootIndicator_le
#print axioms OmegaY.Expansion.build_event_rootIndicator_eq
#print axioms OmegaY.Expansion.build_event_compensated_depth_eq
#print axioms OmegaY.Expansion.build_event_compensated_depth_lt
