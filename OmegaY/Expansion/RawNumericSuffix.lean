/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/RawNumericSuffix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.RawSearchInduction
import OmegaY.Expansion.CanonicalFrontierNumeric

/-!
# Numerical event recovery from a recognized upper region

Raw geometry and backfill are independent of numerical parent recovery.
This module uses recognition only at the specified new event frontiers.
In particular it does not require a normal copied mountain or recognition
of a lower current node. It supplies the numerical suffix needed when a
column proof has already recognized its higher nodes and all earlier columns.
-/

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

theorem eventParentMap_raw_at {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    {bound : Nat} (event : Nat) (column : Fin F.width) (hColumn : column.val ≤ bound) :
    eventParentMap hF hWidth bound event column.val =
      (F.rawParent (eventFrontier hF event column)).map (fun p => p.1.val) := by
  simp only [eventParentMap, frontierParent, if_pos hColumn,
    eventFrontierNat_eq hF hWidth event column.isLt]

/-- Recognition is consulted only at actual frontier nodes in the prefix.
Raw parent closure keeps every numerical record at that same frontier. -/
theorem parentPath_eventFrontier_of_recognition {F : Frame} (hF : F.Ordered)
    (hRaw : F.RawRowGeometry) (hFather : F.RawFatherUpperBound)
    {bound event : Nat}
    (hKnown : ∀ column : Fin F.width, column.val ≤ bound →
      F.rawParent (eventFrontier hF event column) = F.P (eventFrontier hF event column))
    {q p : F.Node} (hFront : eventFrontier hF event q.1 = q) (hBound : q.1.val ≤ bound)
    (path : ParentPath F q p) : eventFrontier hF event p.1 = p := by
  induction path with
  | refl _ => exact hFront
  | @cons q next p hParent rest ih =>
    have hRawParent : F.rawParent (eventFrontier hF event q.1) = some next := by
      rw [hKnown q.1 hBound, hFront]
      exact hParent
    exact ih (eventFrontier_raw_parent_of_bound hF hRaw hFather event q.1 hRawParent)
      ((P_column_lt hF hParent).le.trans hBound)

theorem parentPath_eventParentMap_of_recognition {F : Frame} (hF : F.Ordered)
    (hRaw : F.RawRowGeometry) (hFather : F.RawFatherUpperBound) (hWidth : 0 < F.width)
    {bound event : Nat}
    (hKnown : ∀ column : Fin F.width, column.val ≤ bound →
      F.rawParent (eventFrontier hF event column) = F.P (eventFrontier hF event column))
    {q p : F.Node} (hFront : eventFrontier hF event q.1 = q) (hBound : q.1.val ≤ bound)
    (path : ParentPath F q p) :
    q = p ∨ Ancestor (eventParentMap hF hWidth bound event) q.1.val p.1.val := by
  induction path with
  | refl _ => exact Or.inl rfl
  | @cons q next p hParent rest ih =>
    have hRawParent : F.rawParent (eventFrontier hF event q.1) = some next := by
      rw [hKnown q.1 hBound, hFront]
      exact hParent
    have hMap : eventParentMap hF hWidth bound event q.1.val = some next.1.val := by
      rw [eventParentMap_raw_at hF hWidth event q.1 hBound, hRawParent]
      rfl
    have hNextFront := eventFrontier_raw_parent_of_bound hF hRaw hFather event q.1 hRawParent
    have hNextBound := (P_column_lt hF hParent).le.trans hBound
    rcases ih hNextFront hNextBound with he | ha
    · subst next
      exact Or.inr (.single hMap)
    · exact Or.inr (ancestor_trans (.single hMap) ha)

end OmegaY.Geometry.Frame

namespace OmegaY.Expansion

open Canonical Geometry Frame ZeroY ZeroY.Forest

/-- The numerical event equality uses recognition only at its new frontier.
The old candidate map is the actual raw map, even when its current-column
parent has not yet been recognized. -/
theorem event_numeric_step_of_raw_recognition {mountain : Mountain}
    (hValid : MountainValid mountain) (hSums : MountainSums mountain)
    (hTops : MountainTops mountain) (hRaw : MountainRawGeometry mountain)
    (hFather : (Frame.ofMountain mountain).RawFatherUpperBound)
    (hWidth : 0 < mountain.size) {bound : Nat} (hBound : bound < mountain.size)
    {event : Nat} (hEvent : event < (Frame.ofMountain mountain).lastEvent)
    (hKnown : ∀ column : Fin (Frame.ofMountain mountain).width, column.val ≤ bound →
      (Frame.ofMountain mountain).rawParent (eventFrontier hValid.toOrdered (event + 1) column) =
        (Frame.ofMountain mountain).P (eventFrontier hValid.toOrdered (event + 1) column))
    (column : Fin (Frame.ofMountain mountain).width) (hColumnBound : column.val ≤ bound) :
    nearestSmaller (eventParentMap hValid.toOrdered hWidth bound event)
      (eventValues hValid.toOrdered hWidth (event + 1)) column.val =
        eventParentMap hValid.toOrdered hWidth bound (event + 1) column.val := by
  let F := Frame.ofMountain mountain
  let oldMap := eventParentMap hValid.toOrdered hWidth bound event
  let newMap := eventParentMap hValid.toOrdered hWidth bound (event + 1)
  let values := eventValues hValid.toOrdered hWidth (event + 1)
  have hOldLeft : Leftward oldMap := eventParentMap_leftward hValid.toOrdered hWidth hBound event
  have hNewLeft : Leftward newMap := eventParentMap_leftward hValid.toOrdered hWidth hBound (event + 1)
  generalize hIndex : column.val = index
  induction index using Nat.strongRecOn generalizing column with
  | ind index ih =>
    rw [← hIndex]
    have hPrefix : ∀ i, i < column.val → newMap i = nearestSmaller oldMap values i := by
      intro i hi
      exact (ih i (by omega) ⟨i, hi.trans column.isLt⟩
        (by change i ≤ bound; omega) rfl).symm
    let node := eventFrontier hValid.toOrdered (event + 1) column
    have hCurrent : newMap column.val = (F.rawParent node).map (fun p => p.1.val) :=
      eventParentMap_raw_at hValid.toOrdered hWidth (event + 1) column hColumnBound
    cases hRawParent : F.rawParent node with
    | none =>
      have hOneNode : F.value node = 1 :=
        (hSums.rawParent_none_iff_value_one hValid hTops
          (eventFrontier_spec hValid.toOrdered (event + 1) column).2.1).mp hRawParent
      have hOne : values column.val = 1 := by
        dsimp only [values]
        rw [eventValues_at hValid.toOrdered hWidth (event + 1) column]
        exact hOneNode
      have hNone : newMap column.val = none := by rw [hCurrent, hRawParent]; rfl
      change nearestSmaller oldMap values column.val = newMap column.val
      rw [hNone]
      apply (nearestSmaller_none_iff hOldLeft).mpr
      intro candidate _
      rw [hOne]
      exact eventValues_positive hValid.toOrdered hWidth (event + 1) candidate
    | some parent =>
      have hParent : F.P node = some parent := (hKnown column hColumnBound).symm.trans hRawParent
      have hParentFront : eventFrontier hValid.toOrdered (event + 1) parent.1 = parent :=
        eventFrontier_raw_parent_of_bound hValid.toOrdered hRaw.rawRowGeometry hFather
          (event + 1) column hRawParent
      have hSmall : values parent.1.val < values column.val := by
        dsimp only [values]
        rw [eventValues_at hValid.toOrdered hWidth (event + 1) parent.1, hParentFront,
          eventValues_at hValid.toOrdered hWidth (event + 1) column]
        exact (P_value hValid.toOrdered hParent).2
      have hSome : newMap column.val = some parent.1.val := by rw [hCurrent, hRawParent]; rfl
      change nearestSmaller oldMap values column.val = newMap column.val
      rw [hSome]
      by_cases hChanged : node ≠ eventFrontier hValid.toOrdered event column
      · obtain ⟨oldParent, hOldParent, hCandidate⟩ :=
          hSums.eventFrontier_moving_candidate hValid hEvent column hChanged
        let q := eventFrontier hValid.toOrdered (event + 1) oldParent.1
        have hOldCandidate : oldMap column.val = some q.1.val := by
          dsimp only [oldMap]
          rw [eventParentMap_raw_at hValid.toOrdered hWidth event column hColumnBound, hOldParent]
          rfl
        have hQ : F.Q node = some q := hCandidate
        have hQFront : eventFrontier hValid.toOrdered (event + 1) q.1 = q := rfl
        have hQPositive : 0 < F.value q := hValid.toOrdered.real_positive q
          (eventFrontier_spec hValid.toOrdered (event + 1) oldParent.1).2.1
        obtain ⟨actualQ, hActualQ, trace⟩ := (P_iff hValid.toOrdered).mp hParent
        have hQEq : actualQ = q := Option.some.inj (hActualQ.symm.trans hQ)
        subst actualQ
        rcases trace.parentPath_last_barrier hValid.toOrdered hQPositive with hDirect |
            ⟨z, path, hLast, hBarrier⟩
        · have hDirectMap : oldMap column.val = some parent.1.val := by
            simpa only [hDirect] using hOldCandidate
          exact nearestSmaller_eq_of_direct hOldLeft hDirectMap hSmall
        · have hQBound : q.1.val ≤ bound := (hOldLeft hOldCandidate).le.trans hColumnBound
          have hZFront : eventFrontier hValid.toOrdered (event + 1) z.1 = z :=
            parentPath_eventFrontier_of_recognition hValid.toOrdered hRaw.rawRowGeometry
              hFather hKnown hQFront hQBound path
          have hZBound : z.1.val ≤ bound := (path.column_le hValid.toOrdered).trans hQBound
          have hZParent : newMap z.1.val = some parent.1.val := by
            dsimp only [newMap]
            rw [eventParentMap_raw_at hValid.toOrdered hWidth (event + 1) z.1 hZBound,
              hKnown z.1 hZBound, hZFront, hLast]
            rfl
          have hZ : z.1.val = q.1.val ∨ Ancestor newMap q.1.val z.1.val := by
            rcases parentPath_eventParentMap_of_recognition hValid.toOrdered hRaw.rawRowGeometry
                hFather hWidth hKnown hQFront hQBound path with he | ha
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
            rw [eventValues_at hValid.toOrdered hWidth (event + 1) column,
              eventValues_at hValid.toOrdered hWidth (event + 1) z.1, hZFront]
            exact hBarrier
          exact nearestSmaller_eq_of_blocker hOldLeft hNewLeft hOldCandidate hParentAncestor
            hPrefix hZ hZParent hSmall hUpper
      · have hSame : node = eventFrontier hValid.toOrdered event column := Classical.not_not.mp hChanged
        have hOldParent : oldMap column.val = some parent.1.val := by
          dsimp only [oldMap]
          rw [eventParentMap_raw_at hValid.toOrdered hWidth event column hColumnBound,
            ← hSame, hRawParent]
          rfl
        exact nearestSmaller_eq_of_direct hOldLeft hOldParent hSmall

/-- Recognition on a finite positive suffix gives numerical recovery on
that suffix. Event zero, whose candidates are the bottom legs, is excluded. -/
theorem numeric_suffix_of_frontier_recognition {mountain : Mountain}
    (hValid : MountainValid mountain) (hSums : MountainSums mountain)
    (hTops : MountainTops mountain) (hRaw : MountainRawGeometry mountain)
    (hFather : (Frame.ofMountain mountain).RawFatherUpperBound)
    (hWidth : 0 < mountain.size) {bound start : Nat} (hBound : bound < mountain.size)
    (hStart : 0 < start)
    (hKnown : ∀ event, start ≤ event → event ≤ (Frame.ofMountain mountain).lastEvent →
      ∀ column : Fin (Frame.ofMountain mountain).width, column.val ≤ bound →
        (Frame.ofMountain mountain).rawParent (eventFrontier hValid.toOrdered event column) =
          (Frame.ofMountain mountain).P (eventFrontier hValid.toOrdered event column))
    (initial : ParentMap) :
    Forests.NumericSuffix
      ((Frame.ofMountain mountain).frontierForests initial
        (eventFrontierNat hValid.toOrdered hWidth) bound)
      ((Frame.ofMountain mountain).frontierValue (eventFrontierNat hValid.toOrdered hWidth))
      bound start (Frame.ofMountain mountain).lastEvent := by
  intro event hFrom hFinish column hColumn
  cases event with
  | zero => omega
  | succ previous =>
    exact event_numeric_step_of_raw_recognition hValid hSums hTops hRaw hFather hWidth
      hBound (by omega) (hKnown (previous + 1) hFrom hFinish)
      ⟨column, hColumn.trans_lt hBound⟩ hColumn

theorem eventFrontier_height_monotone {F : Frame} (hF : F.Ordered)
    (column : Fin F.width) : Monotone (fun event => F.height (eventFrontier hF event column)) := by
  intro earlier later hOrder
  have hBefore := eventFrontier_spec hF earlier column
  have hAfter := eventFrontier_spec hF later column
  exact (hF.rows_strict column).monotone
    (hAfter.2.2.2.1 (eventFrontier hF earlier column).2
      (hBefore.2.2.1.trans (F.eventCut_monotone hOrder)))

/-- The exact column/top-down induction interface. Only strictly earlier
columns and strictly higher nodes in the current column are recognized.
The selected suffix must begin above the current node; no lower/current
parent recognition and no output Normal certificate is used. -/
theorem expandDiagram_upper_numeric_suffix {input : List Nat} (hLegal : Canonical.Legal input)
    {copies : Nat} {mountain : Mountain} (hRun : expandDiagram input copies = .ok mountain)
    (current : (Frame.ofMountain mountain).Node) (hReal : Frame.Real current)
    (start : Nat)
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
    Forests.NumericSuffix
      ((Frame.ofMountain mountain).frontierForests initial
        (eventFrontierNat (expandDiagram_valid_of_success hLegal hRun).toOrdered
          ((Nat.zero_le current.1.val).trans_lt current.1.isLt)) current.1.val)
      ((Frame.ofMountain mountain).frontierValue
        (eventFrontierNat (expandDiagram_valid_of_success hLegal hRun).toOrdered
          ((Nat.zero_le current.1.val).trans_lt current.1.isLt)))
      current.1.val start (Frame.ofMountain mountain).lastEvent := by
  let F := Frame.ofMountain mountain
  have hValid := expandDiagram_valid_of_success hLegal hRun
  have hSums := (expandDiagram_equations hLegal hRun).1
  have hTops := (expandDiagram_equations hLegal hRun).2
  have hStart : 0 < start := by
    by_contra hn
    have he : start = 0 := by omega
    have hAtZero := (eventFrontier_spec hValid.toOrdered 0 current.1).2.2.1
    rw [F.eventCut_zero] at hAtZero
    have hOne := one_le_height hValid.toOrdered hReal
    have hAboveZero := hAbove
    rw [he] at hAboveZero
    exact (not_lt_of_ge (hAtZero.trans hOne)) hAboveZero
  apply numeric_suffix_of_frontier_recognition hValid hSums hTops
    (expandDiagram_raw_geometry hLegal hRun) (expandDiagram_raw_father_upper_bound hLegal hRun)
    ((Nat.zero_le current.1.val).trans_lt current.1.isLt) current.1.isLt hStart _ initial
  intro event hFrom _ column hColumn
  let node := eventFrontier hValid.toOrdered event column
  have hNodeReal : Real node := (eventFrontier_spec hValid.toOrdered event column).2.1
  apply hSums.rawParent_eq_P_of_recognition hValid hTops hNodeReal
  intro parent hParent
  rcases lt_or_eq_of_le hColumn with hBefore | hSame
  · exact hLeft node parent hBefore hNodeReal hParent
  · have hColumnEq : column = current.1 := Fin.ext hSame
    have hHigher : F.height current < F.height node := by
      change F.height current < F.height (eventFrontier hValid.toOrdered event column)
      rw [hColumnEq]
      exact hAbove.trans_le (eventFrontier_height_monotone hValid.toOrdered current.1 hFrom)
    exact hHigh node parent hColumnEq hHigher hNodeReal hParent

end OmegaY.Expansion

#print axioms OmegaY.Geometry.Frame.eventParentMap_raw_at
#print axioms OmegaY.Geometry.Frame.parentPath_eventFrontier_of_recognition
#print axioms OmegaY.Geometry.Frame.parentPath_eventParentMap_of_recognition
#print axioms OmegaY.Expansion.event_numeric_step_of_raw_recognition
#print axioms OmegaY.Expansion.numeric_suffix_of_frontier_recognition
#print axioms OmegaY.Expansion.eventFrontier_height_monotone
#print axioms OmegaY.Expansion.expandDiagram_upper_numeric_suffix
