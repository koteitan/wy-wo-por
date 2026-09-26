/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CommonRawParentDepthWord.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.UpperDepthComparison
import OmegaY.Expansion.CommonParentDepthWord

/-!
# Actual common stored parents determine the upper comparison event

This removes the separate starting-candidate equality from the high-event
numerical bridge. Equal actual upper heights and a common stored parent
identify the preceding frontier and its candidate. Only strict-left and
strictly-higher numerical recognition is used; the current lower node is
not assumed recognized. Transporting a source depth-word inequality remains
necessary to conclude a new numerical inequality.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

theorem expandDiagram_common_raw_parent_depthWord
    {input : List Nat} (hLegal : Canonical.Legal input)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram input copies = .ok mountain)
    {u z parent uUpper zUpper : (Frame.ofMountain mountain).Node}
    (hUReal : Real u) (hZReal : Real z) (hZColumn : z.1.val ≤ u.1.val)
    (hUP : (Frame.ofMountain mountain).rawParent u = some parent)
    (hZP : (Frame.ofMountain mountain).rawParent z = some parent)
    (hUUpper : (Frame.ofMountain mountain).upper u = some uUpper)
    (hZUpper : (Frame.ofMountain mountain).upper z = some zUpper)
    (hRows : (Frame.ofMountain mountain).height uUpper = (Frame.ofMountain mountain).height zUpper)
    (hLeft : ∀ (node father : (Frame.ofMountain mountain).Node),
      node.1.val < u.1.val → Real node →
      (Frame.ofMountain mountain).rawParent node = some father →
        (Frame.ofMountain mountain).P node = some father)
    (hHigh : ∀ (node father : (Frame.ofMountain mountain).Node), node.1 = u.1 →
      (Frame.ofMountain mountain).height u < (Frame.ofMountain mountain).height node →
      Real node → (Frame.ofMountain mountain).rawParent node = some father →
        (Frame.ofMountain mountain).P node = some father)
    (initial : ParentMap) :
    let F := Frame.ofMountain mountain
    let hValid := expandDiagram_valid_of_success hLegal hRun
    let hWidth := (Nat.zero_le u.1.val).trans_lt u.1.isLt
    let front := eventFrontierNat hValid.toOrdered hWidth
    let forests := F.frontierForests initial front u.1.val
    ∃ event, event < F.lastEvent ∧ F.eventCut (event + 1) = F.height uUpper ∧
      eventFrontier hValid.toOrdered event u.1 = u ∧
      eventFrontier hValid.toOrdered event z.1 = z ∧
      eventFrontier hValid.toOrdered (event + 1) u.1 = uUpper ∧
      eventFrontier hValid.toOrdered (event + 1) z.1 = zUpper ∧
      forests (event + 1) u.1.val = forests (event + 1) z.1.val ∧
      (Forests.DepthWordLt forests (event + 1) F.lastEvent u.1.val z.1.val ↔ F.value u < F.value z) ∧
      (Forests.DepthWordEq forests (event + 1) F.lastEvent u.1.val z.1.val ↔ F.value u = F.value z) ∧
      (Forests.DepthWordLe forests (event + 1) F.lastEvent u.1.val z.1.val ↔ F.value u ≤ F.value z) := by
  let F := Frame.ofMountain mountain
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hWidth : 0 < mountain.size := (Nat.zero_le u.1.val).trans_lt u.1.isLt
  let front := eventFrontierNat hValid.toOrdered hWidth
  let forests := F.frontierForests initial front u.1.val
  let values := F.frontierValue front
  change ∃ event, event < F.lastEvent ∧ F.eventCut (event + 1) = F.height uUpper ∧
    eventFrontier hValid.toOrdered event u.1 = u ∧ eventFrontier hValid.toOrdered event z.1 = z ∧
    eventFrontier hValid.toOrdered (event + 1) u.1 = uUpper ∧
    eventFrontier hValid.toOrdered (event + 1) z.1 = zUpper ∧
    forests (event + 1) u.1.val = forests (event + 1) z.1.val ∧
    (Forests.DepthWordLt forests (event + 1) F.lastEvent u.1.val z.1.val ↔ F.value u < F.value z) ∧
    (Forests.DepthWordEq forests (event + 1) F.lastEvent u.1.val z.1.val ↔ F.value u = F.value z) ∧
    (Forests.DepthWordLe forests (event + 1) F.lastEvent u.1.val z.1.val ↔ F.value u ≤ F.value z)
  obtain ⟨event, hEvent, hCut, hUFront, hUNext⟩ := upper_at_positive_event hValid.toOrdered hUReal hUUpper
  obtain ⟨hZFront, hZNext⟩ := eventFrontier_pair_of_upper_cut hValid.toOrdered hEvent hZUpper (hCut.trans hRows)
  have hCommon : forests (event + 1) u.1.val = forests (event + 1) z.1.val := by
    change eventParentMap hValid.toOrdered hWidth u.1.val event u.1.val =
      eventParentMap hValid.toOrdered hWidth u.1.val event z.1.val
    rw [eventParentMap_raw_at hValid.toOrdered hWidth event u.1 le_rfl,
      eventParentMap_raw_at hValid.toOrdered hWidth event z.1 hZColumn, hUFront, hZFront, hUP, hZP]
  have hAbove : F.height u < F.height (eventFrontier hValid.toOrdered (event + 1) u.1) := by
    rw [hUNext]
    exact Row.lt_B _ _ |>.trans_eq
      ((expandDiagram_raw_geometry hLegal hRun).rawRowGeometry u uUpper hUReal hUUpper).choose_spec.2.2.2.symm
  have hCompare := expandDiagram_upper_depthWord_comparison hLegal hRun u hUReal (event + 1)
    (Nat.succ_le_of_lt hEvent) hAbove hLeft hHigh initial u.1.val z.1.val le_rfl hZColumn hCommon
  have hUValue : values (event + 1) u.1.val = F.value uUpper := by
    dsimp only [values, frontierValue, front]
    rw [eventFrontierNat_eq hValid.toOrdered hWidth _ u.1.isLt, hUNext]
  have hZValue : values (event + 1) z.1.val = F.value zUpper := by
    dsimp only [values, frontierValue, front]
    rw [eventFrontierNat_eq hValid.toOrdered hWidth _ z.1.isLt, hZNext]
  have hUSum : F.value u = F.value uUpper + F.value parent := by
    obtain ⟨actual, hActual, _, _, _, hSum, _⟩ := (expandDiagram_equations hLegal hRun).1.rawParent_upper hValid hUReal hUUpper
    have he : actual = parent := Option.some.inj (hActual.symm.trans hUP)
    exact he ▸ hSum
  have hZSum : F.value z = F.value zUpper + F.value parent := by
    obtain ⟨actual, hActual, _, _, _, hSum, _⟩ := (expandDiagram_equations hLegal hRun).1.rawParent_upper hValid hZReal hZUpper
    have he : actual = parent := Option.some.inj (hActual.symm.trans hZP)
    exact he ▸ hSum
  change
    (Forests.DepthWordLt forests (event + 1) F.lastEvent u.1.val z.1.val ↔ values (event + 1) u.1.val < values (event + 1) z.1.val) ∧
    (Forests.DepthWordEq forests (event + 1) F.lastEvent u.1.val z.1.val ↔ values (event + 1) u.1.val = values (event + 1) z.1.val) ∧
    (Forests.DepthWordLe forests (event + 1) F.lastEvent u.1.val z.1.val ↔ values (event + 1) u.1.val ≤ values (event + 1) z.1.val) at hCompare
  rw [hUValue, hZValue] at hCompare
  exact ⟨event, hEvent, hCut, hUFront, hZFront, hUNext, hZNext, hCommon,
    hCompare.1.trans (common_parent_backfill_lt_iff hUSum hZSum).symm,
    hCompare.2.1.trans (common_parent_backfill_eq_iff hUSum hZSum).symm,
    hCompare.2.2.trans (common_parent_backfill_le_iff hUSum hZSum).symm⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_common_raw_parent_depthWord
