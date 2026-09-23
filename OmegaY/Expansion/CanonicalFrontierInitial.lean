/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CanonicalFrontierInitial.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CanonicalFrontierNumeric
import OmegaY.Canonical.BottomLegs

/-!
# The real bottom candidate forest and full source-event numeric recovery

Event zero starts from the ordinary left-neighbour candidate map. Exact
bottom legs make its Q step the previous column's bottom node. Together
with the positive-event theorem this supplies all source events, including
zero. No analogous output-canonicality assertion is made.
-/

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

def bottomCandidateMap (bound : Nat) : ParentMap := fun column =>
  if column ≤ bound then if column = 0 then none else some (column - 1) else none

theorem bottomCandidateMap_zero (bound : Nat) : bottomCandidateMap bound 0 = none := by
  simp only [bottomCandidateMap, Nat.zero_le, ↓reduceIte]

theorem bottomCandidateMap_some {bound column : Nat} (hBound : column ≤ bound)
    (hPositive : 0 < column) : bottomCandidateMap bound column = some (column - 1) := by
  simp only [bottomCandidateMap, if_pos hBound, if_neg (Nat.ne_of_gt hPositive)]

theorem bottomCandidateMap_leftward (bound : Nat) : Leftward (bottomCandidateMap bound) := by
  intro column parent hParent
  unfold bottomCandidateMap at hParent
  split at hParent
  · split at hParent
    · cases hParent
    · have hEq := Option.some.inj hParent
      omega
  · cases hParent

/-- The source-side stored bottom leg, stated directly on typed frame
cells. For a successful concrete build it is build_bottom_left. -/
def BottomPredecessorLegs (F : Frame) : Prop :=
  ∀ column (hi : 1 < F.length column),
    (F.cells column ⟨1, hi⟩).left =
      if column.val = 0 then none else some ⟨column.val - 1, 0⟩

theorem eventFrontier_zero_Q {F : Frame} (hF : F.Ordered) (hLegs : BottomPredecessorLegs F)
    (column : Fin F.width) (hPositive : 0 < column.val) :
    F.Q (eventFrontier hF 0 column) =
      some (eventFrontier hF 0 ⟨column.val - 1, (Nat.sub_lt hPositive (by omega)).trans column.isLt⟩) := by
  let previous : Fin F.width := ⟨column.val - 1, (Nat.sub_lt hPositive (by omega)).trans column.isLt⟩
  have hPreviousLength : 1 < F.length previous := by have := hF.length_ge_two previous; omega
  let left : F.Node := ⟨previous, ⟨0, by omega⟩⟩
  rw [eventFrontier_zero hF column, eventFrontier_zero hF previous]
  apply Q_eq_upper_at_equal hF (left := left)
  · change (F.cells column ⟨1, _⟩).left = some (ref left)
    rw [hLegs column _]
    simp only [if_neg (Nat.ne_of_gt hPositive), ref, left, previous]
  · simp only [upper, left, Nat.zero_add, hPreviousLength, ↓reduceDIte]
  · simp only [height, cell, hF.bottom_row]

/-- Actual event-zero recovery from the bottom left-neighbour graph. The
only additional source input is the exact stored bottom leg. -/
theorem Normal.event_numeric_initial {F : Frame} (hF : F.Normal)
    (hLegs : BottomPredecessorLegs F) (hWidth : 0 < F.width)
    {bound : Nat} (hBound : bound < F.width) (column : Fin F.width)
    (hColumnBound : column.val ≤ bound) :
    nearestSmaller (bottomCandidateMap bound) (eventValues hF.toOrdered hWidth 0) column.val =
      eventParentMap hF.toOrdered hWidth bound 0 column.val := by
  let oldMap := bottomCandidateMap bound
  let newMap := eventParentMap hF.toOrdered hWidth bound 0
  let values := eventValues hF.toOrdered hWidth 0
  have hOldLeft : Leftward oldMap := bottomCandidateMap_leftward bound
  have hNewLeft : Leftward newMap := eventParentMap_leftward hF.toOrdered hWidth hBound 0
  generalize hIndex : column.val = index
  induction index using Nat.strongRecOn generalizing column with
  | ind index ih =>
    rw [← hIndex]
    have hPrefix : ∀ i, i < column.val → newMap i = nearestSmaller oldMap values i := by
      intro i hi
      exact (ih i (by omega) ⟨i, hi.trans column.isLt⟩
        (by change i ≤ bound; omega) rfl).symm
    let node := eventFrontier hF.toOrdered 0 column
    have hCurrent : newMap column.val = (F.P node).map (fun p => p.1.val) :=
      hF.eventParentMap_at hWidth 0 column hColumnBound
    cases hParent : F.P node with
    | none =>
      have hPositive := hF.real_positive node (eventFrontier_spec hF.toOrdered 0 column).2.1
      have hNotLarge : ¬ 1 < F.value node := by
        intro hLarge
        obtain ⟨parent, hSome⟩ := hF.parent_exists hLarge
        rw [hParent] at hSome
        cases hSome
      have hOne : values column.val = 1 := by
        dsimp only [values]
        rw [eventValues_at hF.toOrdered hWidth 0 column]
        change F.value node = 1
        omega
      have hNone : newMap column.val = none := by rw [hCurrent, hParent]; rfl
      change nearestSmaller oldMap values column.val = newMap column.val
      rw [hNone]
      apply (nearestSmaller_none_iff hOldLeft).mpr
      intro candidate _
      rw [hOne]
      exact eventValues_positive hF.toOrdered hWidth 0 candidate
    | some parent =>
      have hParentFront : eventFrontier hF.toOrdered 0 parent.1 = parent :=
        hF.eventFrontier_parent 0 column hParent
      have hSmall : values parent.1.val < values column.val := by
        dsimp only [values]
        rw [eventValues_at hF.toOrdered hWidth 0 parent.1, hParentFront,
          eventValues_at hF.toOrdered hWidth 0 column]
        exact (P_value hF.toOrdered hParent).2
      have hSome : newMap column.val = some parent.1.val := by rw [hCurrent, hParent]; rfl
      change nearestSmaller oldMap values column.val = newMap column.val
      rw [hSome]
      have hColumnPositive : 0 < column.val :=
        (Nat.zero_le parent.1.val).trans_lt (P_column_lt hF.toOrdered hParent)
      let previous : Fin F.width :=
        ⟨column.val - 1, (Nat.sub_lt hColumnPositive (by omega)).trans column.isLt⟩
      let q := eventFrontier hF.toOrdered 0 previous
      have hOldCandidate : oldMap column.val = some q.1.val :=
        bottomCandidateMap_some hColumnBound hColumnPositive
      have hQ : F.Q node = some q := eventFrontier_zero_Q hF.toOrdered hLegs column hColumnPositive
      have hQFront : eventFrontier hF.toOrdered 0 q.1 = q := rfl
      have hQPositive : 0 < F.value q :=
        hF.real_positive q (eventFrontier_spec hF.toOrdered 0 previous).2.1
      obtain ⟨actualQ, hActualQ, trace⟩ := (P_iff hF.toOrdered).mp hParent
      have hQEq : actualQ = q := Option.some.inj (hActualQ.symm.trans hQ)
      subst actualQ
      rcases trace.parentPath_last_barrier hF.toOrdered hQPositive with hDirect |
          ⟨z, path, hLast, hBarrier⟩
      · have hDirectMap : oldMap column.val = some parent.1.val := by
          simpa only [hDirect] using hOldCandidate
        exact nearestSmaller_eq_of_direct hOldLeft hDirectMap hSmall
      · have hQBound : q.1.val ≤ bound := (hOldLeft hOldCandidate).le.trans hColumnBound
        have hZFront : eventFrontier hF.toOrdered 0 z.1 = z :=
          hF.parentPath_eventFrontier 0 hQFront path
        have hZBound : z.1.val ≤ bound := (path.column_le hF.toOrdered).trans hQBound
        have hZParent : newMap z.1.val = some parent.1.val := by
          dsimp only [newMap]
          rw [hF.eventParentMap_at hWidth 0 z.1 hZBound, hZFront, hLast]
          rfl
        have hZ : z.1.val = q.1.val ∨ Ancestor newMap q.1.val z.1.val := by
          rcases hF.parentPath_eventParentMap hWidth hQFront hQBound path with he | ha
          · exact Or.inl (congrArg (fun u : F.Node => u.1.val) he.symm)
          · exact Or.inr ha
        have hCurrentPath : Ancestor newMap q.1.val parent.1.val := by
          rcases hZ with he | ha
          · exact .single (by simpa only [he] using hZParent)
          · exact ancestor_trans ha (.single hZParent)
        have hRecoveredPath : Ancestor (nearestSmaller oldMap values) q.1.val parent.1.val :=
          ancestor_transfer_prefix hNewLeft (hOldLeft hOldCandidate) hPrefix hCurrentPath
        have hParentAncestor : Ancestor oldMap column.val parent.1.val :=
          ancestor_trans (.single hOldCandidate) (nearestSmaller_ancestor_lift hOldLeft hRecoveredPath)
        have hUpper : values column.val ≤ values z.1.val := by
          dsimp only [values]
          rw [eventValues_at hF.toOrdered hWidth 0 column,
            eventValues_at hF.toOrdered hWidth 0 z.1, hZFront]
          exact hBarrier
        exact nearestSmaller_eq_of_blocker hOldLeft hNewLeft hOldCandidate hParentAncestor
          hPrefix hZ hZParent hSmall hUpper

/-- Full source NumericSuffix including its actual bottom initialization. -/
theorem Normal.event_numeric_full {F : Frame} (hF : F.Normal)
    (hLegs : BottomPredecessorLegs F) (hWidth : 0 < F.width)
    {bound : Nat} (hBound : bound < F.width) :
    Forests.NumericSuffix
      (F.frontierForests (bottomCandidateMap bound) (eventFrontierNat hF.toOrdered hWidth) bound)
      (F.frontierValue (eventFrontierNat hF.toOrdered hWidth)) bound 0 F.lastEvent := by
  intro event _ hFinish column hColumn
  cases event with
  | zero =>
    exact hF.event_numeric_initial hLegs hWidth hBound
      ⟨column, hColumn.trans_lt hBound⟩ hColumn
  | succ previous =>
    exact hF.event_numeric_step hWidth hBound (by omega)
      ⟨column, hColumn.trans_lt hBound⟩ hColumn

end OmegaY.Geometry.Frame

namespace OmegaY.Canonical

open Geometry

theorem build_bottomPredecessorLegs {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) : Frame.BottomPredecessorLegs (Frame.ofMountain mountain) :=
  build_bottom_left hBuild

theorem build_eventFrontier_numeric_full {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) (hWidth : 0 < mountain.size)
    {bound : Nat} (hBound : bound < mountain.size) :
    Forests.NumericSuffix
      ((Frame.ofMountain mountain).frontierForests (Frame.bottomCandidateMap bound)
        (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth) bound)
      ((Frame.ofMountain mountain).frontierValue
        (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth))
      bound 0 (Frame.ofMountain mountain).lastEvent :=
  (build_normal_of_success hBuild).event_numeric_full (build_bottomPredecessorLegs hBuild) hWidth hBound

end OmegaY.Canonical

namespace OmegaY.Expansion

open Canonical Geometry

/-- For an actual canonical source, event-depth words compare the actual
frontier values on any suffix whose two starting candidate parents agree.
All numeric, synchronization, and terminal-one premises are supplied here.
The common-parent premise is retained explicitly. -/
theorem build_eventDepth_value_comparison {input : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build input = .ok mountain) (hWidth : 0 < mountain.size)
    {bound : Nat} (hBound : bound < mountain.size) :
    let F := Frame.ofMountain mountain
    let front := Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth
    let forests := F.frontierForests (Frame.bottomCandidateMap bound) front bound
    let values := F.frontierValue front
    ∀ start c z, start ≤ F.lastEvent → c ≤ bound → z ≤ bound →
      forests start c = forests start z →
      (Forests.DepthWordLt forests start F.lastEvent c z ↔ values start c < values start z) ∧
      (Forests.DepthWordEq forests start F.lastEvent c z ↔ values start c = values start z) ∧
      (Forests.DepthWordLe forests start F.lastEvent c z ↔ values start c ≤ values start z) := by
  let F := Frame.ofMountain mountain
  have hNormal := build_normal_of_success hBuild
  let front := Frame.eventFrontierNat hNormal.toOrdered hWidth
  let forests := F.frontierForests (Frame.bottomCandidateMap bound) front bound
  let values := F.frontierValue front
  change ∀ start c z, start ≤ F.lastEvent → c ≤ bound → z ≤ bound →
    forests start c = forests start z →
    (Forests.DepthWordLt forests start F.lastEvent c z ↔ values start c < values start z) ∧
    (Forests.DepthWordEq forests start F.lastEvent c z ↔ values start c = values start z) ∧
    (Forests.DepthWordLe forests start F.lastEvent c z ↔ values start c ≤ values start z)
  intro start c z hStart hc hz hParent
  have hColumns : ∀ event column, column ≤ bound → (front event column).1.val = column := by
    intro event column hColumn
    dsimp only [front]
    rw [Frame.eventFrontierNat_eq hNormal.toOrdered hWidth event (hColumn.trans_lt hBound)]
    rfl
  have hLeft : ∀ event, start ≤ event → event ≤ F.lastEvent →
      ZeroY.Forest.Leftward (forests event) := by
    intro event _ _
    exact Frame.frontierForests_leftward hNormal.toOrdered
      (Frame.bottomCandidateMap_leftward bound) hColumns event
  have hFullNumeric : Forests.NumericSuffix forests values bound 0 F.lastEvent :=
    build_eventFrontier_numeric_full hBuild hWidth hBound
  have hNumeric : Forests.NumericSuffix forests values bound start F.lastEvent := by
    intro event _ hFinish column hColumn
    exact hFullNumeric event (Nat.zero_le _) hFinish column hColumn
  have hFullBackfill : Forests.SynchronousBackfill forests values
      (Frame.frontierMoves front) bound 0 F.lastEvent :=
    build_eventFrontier_synchronousBackfill hBuild hWidth hBound (Frame.bottomCandidateMap bound)
  have hBackfill : Forests.SynchronousBackfill forests values
      (Frame.frontierMoves front) bound start F.lastEvent := {
    stationary := fun event _ hFinish column hColumn hStay =>
      hFullBackfill.stationary event (Nat.zero_le _) hFinish column hColumn hStay
    moving := fun event _ hFinish column hColumn hMove =>
      hFullBackfill.moving event (Nat.zero_le _) hFinish column hColumn hMove
    synchronous := fun event _ hFinish column other hColumn hOther hSame =>
      hFullBackfill.synchronous event (Nat.zero_le _) hFinish column other hColumn hOther hSame }
  have hTerminalColumn : ∀ column, column ≤ bound → values F.lastEvent column = 1 := by
    intro column hColumn
    have hRead : values F.lastEvent column =
        F.value (Frame.eventFrontier hNormal.toOrdered F.lastEvent
          ⟨column, hColumn.trans_lt hBound⟩) :=
      Frame.eventValues_at hNormal.toOrdered hWidth F.lastEvent ⟨column, hColumn.trans_lt hBound⟩
    exact hRead.trans (hNormal.eventFrontier_last_value ⟨column, hColumn.trans_lt hBound⟩)
  have hTerminal : values F.lastEvent c = values F.lastEvent z :=
    (hTerminalColumn c hc).trans (hTerminalColumn z hz).symm
  exact ⟨Forests.depthWordLt_iff_value_lt hLeft hNumeric hBackfill hc hz hStart hParent hTerminal,
    Forests.depthWordEq_iff_value_eq hLeft hNumeric hBackfill hc hz hStart hParent hTerminal,
    Forests.depthWordLe_iff_value_le hLeft hNumeric hBackfill hc hz hStart hParent hTerminal⟩

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.eventFrontier_zero_Q
#print axioms OmegaY.Geometry.Frame.Normal.event_numeric_initial
#print axioms OmegaY.Geometry.Frame.Normal.event_numeric_full
#print axioms OmegaY.Canonical.build_eventFrontier_numeric_full
#print axioms OmegaY.Expansion.build_eventDepth_value_comparison
