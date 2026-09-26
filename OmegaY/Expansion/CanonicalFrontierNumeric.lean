/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/CanonicalFrontierNumeric.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.CanonicalFrontier
import OmegaY.Geometry.RecordBarrier

/-!
# Numerical recovery at actual canonical source events

The candidate forest for a positive event is the actual raw-parent forest
of the previous frontier. The values are those of the new frontier. Source
Normal, rather than a numerical-suffix hypothesis, supplies the real search
records. Event zero and its separate bottom-leg initialization are excluded.
-/

namespace OmegaY.Geometry.Frame

open ZeroY ZeroY.Forest

/-- Compress a genuine successful Q trace, retaining a last rejected
numerical-parent record and its threshold barrier. -/
theorem Hit.parentPath_last_barrier {F : Frame} (hF : F.Ordered)
    {threshold : Nat} {q p : F.Node} (hPositive : 0 < F.value q)
    (trace : Hit F threshold q p) :
    q = p ∨ ∃ z, ParentPath F q z ∧ F.P z = some p ∧ threshold ≤ F.value z := by
  generalize hc : q.1.val = column
  induction column using Nat.strongRecOn generalizing q with
  | ind column ih =>
    cases trace with
    | here _ _ => exact Or.inl rfl
    | @next q next p hReject hQ rest =>
      have hThreshold : threshold ≤ F.value q := by omega
      obtain ⟨record, wide, tail⟩ := rest.loosen hThreshold
      have hParent : F.P q = some record := (P_iff hF).mpr ⟨next, hQ, wide⟩
      have hRecordLeft : record.1.val < column := by
        simpa only [hc] using P_column_lt hF hParent
      rcases ih record.1.val hRecordLeft (P_value hF hParent).1 tail rfl with he |
          ⟨z, path, hLast, hBarrier⟩
      · subst record
        exact Or.inr ⟨q, .refl _, hParent, hThreshold⟩
      · exact Or.inr ⟨z, .cons hParent path, hLast, hBarrier⟩

noncomputable def eventParentMap {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    (bound event : Nat) : ParentMap :=
  F.frontierParent (eventFrontierNat hF hWidth) bound event

noncomputable def eventValues {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    (event : Nat) : Nat → Nat := F.frontierValue (eventFrontierNat hF hWidth) event

theorem eventValues_at {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    (event : Nat) (column : Fin F.width) :
    eventValues hF hWidth event column.val = F.value (eventFrontier hF event column) := by
  simp only [eventValues, frontierValue, eventFrontierNat_eq hF hWidth event column.isLt]

theorem eventValues_positive {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    (event column : Nat) : 0 < eventValues hF hWidth event column :=
  hF.real_positive _ (eventFrontier_spec hF event
    ⟨min column (F.width - 1), (Nat.min_le_right _ _).trans_lt (by omega)⟩).2.1

theorem Normal.eventParentMap_at {F : Frame} (hF : F.Normal) (hWidth : 0 < F.width)
    {bound : Nat} (event : Nat) (column : Fin F.width) (hColumn : column.val ≤ bound) :
    eventParentMap hF.toOrdered hWidth bound event column.val =
      (F.P (eventFrontier hF.toOrdered event column)).map (fun p => p.1.val) := by
  simp only [eventParentMap, frontierParent, if_pos hColumn,
    eventFrontierNat_eq hF.toOrdered hWidth event column.isLt,
    hF.rawParent_eq_P (eventFrontier_spec hF.toOrdered event column).2.1]

theorem eventParentMap_leftward {F : Frame} (hF : F.Ordered) (hWidth : 0 < F.width)
    {bound : Nat} (hBound : bound < F.width) (event : Nat) :
    Leftward (eventParentMap hF hWidth bound event) := by
  apply frontierParent_leftward hF
  intro column hColumn
  rw [eventFrontierNat_eq hF hWidth event (hColumn.trans_lt hBound)]
  exact congrArg Fin.val (eventFrontier_spec hF event ⟨column, hColumn.trans_lt hBound⟩).1

theorem Normal.parentPath_eventFrontier {F : Frame} (hF : F.Normal) (event : Nat)
    {q p : F.Node} (hFront : eventFrontier hF.toOrdered event q.1 = q)
    (path : ParentPath F q p) : eventFrontier hF.toOrdered event p.1 = p := by
  induction path with
  | refl _ => exact hFront
  | @cons q next p hParent rest ih =>
    apply ih
    apply hF.eventFrontier_parent event q.1
    simpa only [hFront] using hParent

/-- Projection loses no chosen node: source parent closure identifies every
record on this path with its actual event-frontier occurrence. -/
theorem Normal.parentPath_eventParentMap {F : Frame} (hF : F.Normal) (hWidth : 0 < F.width)
    {bound event : Nat} {q p : F.Node}
    (hFront : eventFrontier hF.toOrdered event q.1 = q) (hBound : q.1.val ≤ bound)
    (path : ParentPath F q p) :
    q = p ∨ Ancestor (eventParentMap hF.toOrdered hWidth bound event) q.1.val p.1.val := by
  induction path with
  | refl _ => exact Or.inl rfl
  | @cons q next p hParent rest ih =>
    have hMap : eventParentMap hF.toOrdered hWidth bound event q.1.val = some next.1.val := by
      rw [hF.eventParentMap_at hWidth event q.1 hBound, hFront, hParent]
      rfl
    have hNextFront : eventFrontier hF.toOrdered event next.1 = next := by
      apply hF.eventFrontier_parent event q.1
      simpa only [hFront] using hParent
    have hNextBound : next.1.val ≤ bound := (P_column_lt hF.toOrdered hParent).le.trans hBound
    rcases ih hNextFront hNextBound with he | ha
    · subst next
      exact Or.inr (.single hMap)
    · exact Or.inr (ancestor_trans (.single hMap) ha)

/-- A moving node's first actual Q candidate is the new frontier in the
column of its old P parent. The whole column is read at the new common cut. -/
theorem Normal.eventFrontier_moving_candidate {F : Frame} (hF : F.Normal)
    {event : Nat} (hEvent : event < F.lastEvent) (column : Fin F.width)
    (hChanged : eventFrontier hF.toOrdered (event + 1) column ≠
      eventFrontier hF.toOrdered event column) :
    ∃ parent, F.P (eventFrontier hF.toOrdered event column) = some parent ∧
      F.Q (eventFrontier hF.toOrdered (event + 1) column) =
        some (eventFrontier hF.toOrdered (event + 1) parent.1) := by
  obtain ⟨hUpper, hNewRow⟩ := eventFrontier_advance hF.toOrdered hEvent column hChanged
  obtain ⟨parent, hParent, _, _, _⟩ := hF.upper_step _ _
    (eventFrontier_spec hF.toOrdered event column).2.1 hUpper
  obtain ⟨q, hQ, hColumn⟩ : ∃ q,
      F.Q (eventFrontier hF.toOrdered (event + 1) column) = some q ∧ q.1 = parent.1 := by
    rcases candidate_after_upper hF hParent hUpper with hDirect | ⟨plus, hPlus, _, hQ⟩
    · exact ⟨parent, hDirect, rfl⟩
    · exact ⟨plus, hQ, (upper_spec hPlus).1⟩
  have hFront : eventFrontier hF.toOrdered (event + 1) q.1 = q := by
    apply frontierAt_eq_of_upper_barrier hF.toOrdered (F.eventCut_one_le (event + 1))
    · exact (Q_height_le hF.toOrdered hQ).trans_eq hNewRow
    · intro upper hUpper
      rw [← hNewRow]
      exact Q_upper_gt hF.toOrdered hQ hUpper
  rw [hColumn] at hFront
  exact ⟨parent, hParent, hQ.trans (congrArg some hFront.symm)⟩

/-- Exact numerical recovery for one positive source event. The induction
only uses already recovered columns strictly to the left of the current
column. Stationary columns accept their unchanged parent immediately;
moving columns use the genuine Q trace and its final record barrier. -/
theorem Normal.event_numeric_step {F : Frame} (hF : F.Normal) (hWidth : 0 < F.width)
    {bound : Nat} (hBound : bound < F.width) {event : Nat} (hEvent : event < F.lastEvent)
    (column : Fin F.width) (hColumnBound : column.val ≤ bound) :
    nearestSmaller (eventParentMap hF.toOrdered hWidth bound event)
      (eventValues hF.toOrdered hWidth (event + 1)) column.val =
      eventParentMap hF.toOrdered hWidth bound (event + 1) column.val := by
  let oldMap := eventParentMap hF.toOrdered hWidth bound event
  let newMap := eventParentMap hF.toOrdered hWidth bound (event + 1)
  let values := eventValues hF.toOrdered hWidth (event + 1)
  have hOldLeft : Leftward oldMap := eventParentMap_leftward hF.toOrdered hWidth hBound event
  have hNewLeft : Leftward newMap := eventParentMap_leftward hF.toOrdered hWidth hBound (event + 1)
  generalize hIndex : column.val = index
  induction index using Nat.strongRecOn generalizing column with
  | ind index ih =>
    rw [← hIndex]
    have hPrefix : ∀ i, i < column.val → newMap i = nearestSmaller oldMap values i := by
      intro i hi
      exact (ih i (by omega) ⟨i, hi.trans column.isLt⟩
        (by change i ≤ bound; omega) rfl).symm
    let node := eventFrontier hF.toOrdered (event + 1) column
    have hCurrent : newMap column.val = (F.P node).map (fun p => p.1.val) :=
      hF.eventParentMap_at hWidth (event + 1) column hColumnBound
    cases hParent : F.P node with
    | none =>
      have hPositive := hF.real_positive node (eventFrontier_spec hF.toOrdered (event + 1) column).2.1
      have hNotLarge : ¬ 1 < F.value node := by
        intro hLarge
        obtain ⟨parent, hSome⟩ := hF.parent_exists hLarge
        rw [hParent] at hSome
        cases hSome
      have hOne : values column.val = 1 := by
        dsimp only [values]
        rw [eventValues_at hF.toOrdered hWidth (event + 1) column]
        change F.value node = 1
        omega
      have hNone : newMap column.val = none := by rw [hCurrent, hParent]; rfl
      change nearestSmaller oldMap values column.val = newMap column.val
      rw [hNone]
      apply (nearestSmaller_none_iff hOldLeft).mpr
      intro candidate _
      rw [hOne]
      exact eventValues_positive hF.toOrdered hWidth (event + 1) candidate
    | some parent =>
      have hParentFront : eventFrontier hF.toOrdered (event + 1) parent.1 = parent :=
        hF.eventFrontier_parent (event + 1) column hParent
      have hSmall : values parent.1.val < values column.val := by
        dsimp only [values]
        rw [eventValues_at hF.toOrdered hWidth (event + 1) parent.1, hParentFront,
          eventValues_at hF.toOrdered hWidth (event + 1) column]
        exact (P_value hF.toOrdered hParent).2
      have hSome : newMap column.val = some parent.1.val := by rw [hCurrent, hParent]; rfl
      change nearestSmaller oldMap values column.val = newMap column.val
      rw [hSome]
      by_cases hChanged : node ≠ eventFrontier hF.toOrdered event column
      · obtain ⟨oldParent, hOldParent, hCandidate⟩ :=
          hF.eventFrontier_moving_candidate hEvent column hChanged
        let q := eventFrontier hF.toOrdered (event + 1) oldParent.1
        have hOldCandidate : oldMap column.val = some q.1.val := by
          dsimp only [oldMap]
          rw [hF.eventParentMap_at hWidth event column hColumnBound, hOldParent]
          rfl
        have hQ : F.Q node = some q := hCandidate
        have hQFront : eventFrontier hF.toOrdered (event + 1) q.1 = q := rfl
        have hQPositive : 0 < F.value q :=
          hF.real_positive q (eventFrontier_spec hF.toOrdered (event + 1) oldParent.1).2.1
        obtain ⟨actualQ, hActualQ, trace⟩ := (P_iff hF.toOrdered).mp hParent
        have hQEq : actualQ = q := Option.some.inj (hActualQ.symm.trans hQ)
        subst actualQ
        rcases trace.parentPath_last_barrier hF.toOrdered hQPositive with hDirect |
            ⟨z, path, hLast, hBarrier⟩
        · have hDirectMap : oldMap column.val = some parent.1.val := by
            simpa only [hDirect] using hOldCandidate
          exact nearestSmaller_eq_of_direct hOldLeft hDirectMap hSmall
        · have hQBound : q.1.val ≤ bound := (hOldLeft hOldCandidate).le.trans hColumnBound
          have hZFront : eventFrontier hF.toOrdered (event + 1) z.1 = z :=
            hF.parentPath_eventFrontier (event + 1) hQFront path
          have hZBound : z.1.val ≤ bound := (path.column_le hF.toOrdered).trans hQBound
          have hZParent : newMap z.1.val = some parent.1.val := by
            dsimp only [newMap]
            rw [hF.eventParentMap_at hWidth (event + 1) z.1 hZBound, hZFront, hLast]
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
            rw [eventValues_at hF.toOrdered hWidth (event + 1) column,
              eventValues_at hF.toOrdered hWidth (event + 1) z.1, hZFront]
            exact hBarrier
          exact nearestSmaller_eq_of_blocker hOldLeft hNewLeft hOldCandidate hParentAncestor
            hPrefix hZ hZParent hSmall hUpper
      · have hSame : node = eventFrontier hF.toOrdered event column := Classical.not_not.mp hChanged
        have hOldParent : oldMap column.val = some parent.1.val := by
          dsimp only [oldMap]
          rw [hF.eventParentMap_at hWidth event column hColumnBound, ← hSame, hParent]
          rfl
        exact nearestSmaller_eq_of_direct hOldLeft hOldParent hSmall

/-- Every positive event of a canonical source satisfies NumericSuffix.
The arbitrary initial map is never read on this interval: at event r+1 the
candidate forest is the actual raw-parent forest of frontier r. -/
theorem Normal.event_numeric_suffix {F : Frame} (hF : F.Normal) (hWidth : 0 < F.width)
    {bound : Nat} (hBound : bound < F.width) (initial : ParentMap) :
    Forests.NumericSuffix
      (F.frontierForests initial (eventFrontierNat hF.toOrdered hWidth) bound)
      (F.frontierValue (eventFrontierNat hF.toOrdered hWidth)) bound 1 F.lastEvent := by
  intro event hPositive hFinish column hColumn
  cases event with
  | zero => omega
  | succ previous =>
    exact hF.event_numeric_step hWidth hBound (by omega)
      ⟨column, hColumn.trans_lt hBound⟩ hColumn

end OmegaY.Geometry.Frame

namespace OmegaY.Canonical

open Geometry

theorem build_eventFrontier_numeric_suffix {values : List Nat} {mountain : Mountain}
    (hBuild : build values = .ok mountain) (hWidth : 0 < mountain.size)
    {bound : Nat} (hBound : bound < mountain.size) (initial : ZeroY.ParentMap) :
    Forests.NumericSuffix
      ((Frame.ofMountain mountain).frontierForests initial
        (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth) bound)
      ((Frame.ofMountain mountain).frontierValue
        (Frame.eventFrontierNat (build_normal_of_success hBuild).toOrdered hWidth))
      bound 1 (Frame.ofMountain mountain).lastEvent :=
  (build_normal_of_success hBuild).event_numeric_suffix hWidth hBound initial

end OmegaY.Canonical

#print axioms OmegaY.Geometry.Frame.Hit.parentPath_last_barrier
#print axioms OmegaY.Geometry.Frame.Normal.parentPath_eventParentMap
#print axioms OmegaY.Geometry.Frame.Normal.eventFrontier_moving_candidate
#print axioms OmegaY.Geometry.Frame.Normal.event_numeric_step
#print axioms OmegaY.Geometry.Frame.Normal.event_numeric_suffix
#print axioms OmegaY.Canonical.build_eventFrontier_numeric_suffix
