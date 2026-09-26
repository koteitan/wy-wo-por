/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/UpperDepthComparison.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawNumericSuffix

/-!
# Value comparisons in an already recognized upper region

Actual finite events, raw geometry, backfill and top values provide the
depth-word comparison bridge. The only numerical recognition assumptions
are strictly left of the current column or strictly above the current node.
The starting candidate equality and the copied depth-word order still have
to be supplied by the source-to-copy transport argument.
-/

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- The actual expanded graph supplies all event and backfill hypotheses.
No NumericSuffix or normality of the whole graph is an input. -/
theorem expandDiagram_upper_depthWord_comparison {input : List Nat}
    (hLegal : Canonical.Legal input) {copies : Nat} {mountain : Mountain}
    (hRun : expandDiagram input copies = .ok mountain)
    (current : (Frame.ofMountain mountain).Node) (hReal : Frame.Real current)
    (start : Nat) (hFinish : start ≤ (Frame.ofMountain mountain).lastEvent)
    (hAbove : (Frame.ofMountain mountain).height current <
      (Frame.ofMountain mountain).height
        (eventFrontier (expandDiagram_valid_of_success hLegal hRun).toOrdered start current.1))
    (hLeft : ∀ (node parent : (Frame.ofMountain mountain).Node),
      node.1.val < current.1.val → Frame.Real node →
      (Frame.ofMountain mountain).rawParent node = some parent →
        (Frame.ofMountain mountain).P node = some parent)
    (hHigh : ∀ (node parent : (Frame.ofMountain mountain).Node), node.1 = current.1 →
      (Frame.ofMountain mountain).height current < (Frame.ofMountain mountain).height node →
      Frame.Real node → (Frame.ofMountain mountain).rawParent node = some parent →
        (Frame.ofMountain mountain).P node = some parent)
    (initial : ParentMap) :
    let F := Frame.ofMountain mountain
    let hValid := expandDiagram_valid_of_success hLegal hRun
    let hWidth := (Nat.zero_le current.1.val).trans_lt current.1.isLt
    let front := eventFrontierNat hValid.toOrdered hWidth
    let forests := F.frontierForests initial front current.1.val
    let values := F.frontierValue front
    ∀ c z, c ≤ current.1.val → z ≤ current.1.val →
      forests start c = forests start z →
      (Forests.DepthWordLt forests start F.lastEvent c z ↔ values start c < values start z) ∧
      (Forests.DepthWordEq forests start F.lastEvent c z ↔ values start c = values start z) ∧
      (Forests.DepthWordLe forests start F.lastEvent c z ↔ values start c ≤ values start z) := by
  let F := Frame.ofMountain mountain
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hWidth : 0 < mountain.size := (Nat.zero_le current.1.val).trans_lt current.1.isLt
  let front := eventFrontierNat hValid.toOrdered hWidth
  let forests := F.frontierForests initial front current.1.val
  let values := F.frontierValue front
  change ∀ c z, c ≤ current.1.val → z ≤ current.1.val → forests start c = forests start z →
    (Forests.DepthWordLt forests start F.lastEvent c z ↔ values start c < values start z) ∧
    (Forests.DepthWordEq forests start F.lastEvent c z ↔ values start c = values start z) ∧
    (Forests.DepthWordLe forests start F.lastEvent c z ↔ values start c ≤ values start z)
  intro c z hc hz hCommon
  have hStart : 0 < start := by
    by_contra hn
    have he : start = 0 := by omega
    have hAtZero := (eventFrontier_spec hValid.toOrdered 0 current.1).2.2.1
    rw [F.eventCut_zero] at hAtZero
    have hOne := one_le_height hValid.toOrdered hReal
    have hAboveZero := hAbove
    rw [he] at hAboveZero
    exact (not_lt_of_ge (hAtZero.trans hOne)) hAboveZero
  have hForestLeft : ∀ event, start ≤ event → event ≤ F.lastEvent → Leftward (forests event) := by
    intro event hFrom _
    cases event with
    | zero => omega
    | succ previous =>
      exact eventParentMap_leftward hValid.toOrdered hWidth current.1.isLt previous
  have hNumeric : Forests.NumericSuffix forests values current.1.val start F.lastEvent :=
    expandDiagram_upper_numeric_suffix hLegal hRun current hReal start hAbove hLeft hHigh initial
  have hFullBackfill := expandDiagram_event_synchronousBackfill hLegal hRun hWidth current.1.isLt initial
  have hBackfill : Forests.SynchronousBackfill forests values (frontierMoves front)
      current.1.val start F.lastEvent := {
    stationary := fun event _ hFinish column hColumn hStay =>
      hFullBackfill.stationary event (Nat.zero_le _) hFinish column hColumn hStay
    moving := fun event _ hFinish column hColumn hMove =>
      hFullBackfill.moving event (Nat.zero_le _) hFinish column hColumn hMove
    synchronous := fun event _ hFinish column other hColumn hOther hSame =>
      hFullBackfill.synchronous event (Nat.zero_le _) hFinish column other hColumn hOther hSame }
  have hTerminalColumn : ∀ column, column ≤ current.1.val → values F.lastEvent column = 1 := by
    intro column hColumn
    have hRead : values F.lastEvent column = F.value
        (eventFrontier hValid.toOrdered F.lastEvent ⟨column, hColumn.trans_lt current.1.isLt⟩) :=
      eventValues_at hValid.toOrdered hWidth F.lastEvent ⟨column, hColumn.trans_lt current.1.isLt⟩
    exact hRead.trans (expandDiagram_event_terminal_one hLegal hRun
      ⟨column, hColumn.trans_lt current.1.isLt⟩)
  have hTerminal : values F.lastEvent c = values F.lastEvent z :=
    (hTerminalColumn c hc).trans (hTerminalColumn z hz).symm
  exact ⟨Forests.depthWordLt_iff_value_lt hForestLeft hNumeric hBackfill hc hz hFinish hCommon hTerminal,
    Forests.depthWordEq_iff_value_eq hForestLeft hNumeric hBackfill hc hz hFinish hCommon hTerminal,
    Forests.depthWordLe_iff_value_le hForestLeft hNumeric hBackfill hc hz hFinish hCommon hTerminal⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.expandDiagram_upper_depthWord_comparison
