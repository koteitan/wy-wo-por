/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Forests/EventProjection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: `YesMetaZFC.BMS.transGen_head` is replaced by the lemma `Por.BMS.transGen_head` of this repository, which has the same statement.
-/
import OmegaY.Forests.DepthValues

/-!
# Projecting event parent edges to earlier event paths

A parent edge produced by `nearestSmaller` abbreviates a nonempty path in
the previous forest. Every departure on that path, including its first
vertex but excluding the final parent, is blocked at the original child's
value. Finite event projection preserves this numerical barrier because
additive backfill makes values weakly decrease as event indices increase.

All numeric recovery and backfill assumptions are confined to the stated
finite event suffix and column prefix. The construction does not assume a
projected path, a barrier, or canonicality of a new mountain. Applying it to
copied physical nodes still requires their event/frontier identification.
-/

namespace OmegaY.Forests

open ZeroY
open ZeroY.Forest

/-- A nonempty actual parent path with a lower value bound on every
departure vertex. Its final endpoint is deliberately excluded. -/
def BarrierPath (parent : ParentMap) (value : Nat → Nat) (threshold : Nat)
    (child ancestor : Nat) : Prop :=
  Relation.TransGen
    (fun a b => parent a = some b ∧ threshold ≤ value a) child ancestor

/-- Prefix-local leftwardness keeps an actual ancestor path in that prefix.
No behavior of the parent map beyond the bound is required. -/
theorem ancestor_lt_of_leftward_prefix {parent : ParentMap}
    {bound child found : Nat}
    (hLeft : ∀ ⦃c p⦄, c ≤ bound → parent c = some p → p < c)
    (hc : child ≤ bound) (hPath : Ancestor parent child found) : found < child := by
  induction hPath with
  | single edge => exact hLeft hc edge
  | @tail middle last path edge ih =>
      exact Nat.lt_trans (hLeft (by omega) edge) ih

namespace BarrierPath

theorem ancestor {parent : ParentMap} {value : Nat → Nat}
    {threshold child found : Nat}
    (h : BarrierPath parent value threshold child found) :
    Ancestor parent child found := by
  induction h with
  | single edge => exact Relation.TransGen.single edge.1
  | tail _ edge ih => exact Relation.TransGen.tail ih edge.1

theorem trans {parent : ParentMap} {value : Nat → Nat}
    {threshold child middle found : Nat}
    (h₁ : BarrierPath parent value threshold child middle)
    (h₂ : BarrierPath parent value threshold middle found) :
    BarrierPath parent value threshold child found :=
  Relation.TransGen.trans h₁ h₂

/-- Leftwardness ensures that every vertex whose value is changed remains
inside the original bounded prefix. -/
theorem map_values {parent : ParentMap} {value newValue : Nat → Nat}
    {threshold child found bound : Nat} (hLeft : Leftward parent)
    (hc : child ≤ bound)
    (hMono : ∀ c, c ≤ bound → value c ≤ newValue c)
    (h : BarrierPath parent value threshold child found) :
    BarrierPath parent newValue threshold child found := by
  induction h with
  | single edge =>
      exact Relation.TransGen.single ⟨edge.1, Nat.le_trans edge.2 (hMono _ hc)⟩
  | @tail middle last path edge ih =>
      have hm := ancestor_lt hLeft (BarrierPath.ancestor path)
      exact Relation.TransGen.tail ih
        ⟨edge.1, Nat.le_trans edge.2 (hMono middle (by omega))⟩

theorem weaken {parent : ParentMap} {value : Nat → Nat}
    {threshold newThreshold child found : Nat} (hLe : newThreshold ≤ threshold)
    (h : BarrierPath parent value threshold child found) :
    BarrierPath parent value newThreshold child found := by
  induction h with
  | single edge => exact Relation.TransGen.single ⟨edge.1, Nat.le_trans hLe edge.2⟩
  | tail _ edge ih => exact Relation.TransGen.tail ih ⟨edge.1, Nat.le_trans hLe edge.2⟩

/-- The last departure on the projected path is an actual direct child of
the endpoint and retains the same numerical barrier. -/
theorem exists_last_edge {parent : ParentMap} {value : Nat → Nat}
    {threshold child found : Nat}
    (h : BarrierPath parent value threshold child found) :
    ∃ z, (z = child ∨ Ancestor parent child z) ∧
      parent z = some found ∧ threshold ≤ value z := by
  cases h with
  | single edge => exact ⟨_, Or.inl rfl, edge⟩
  | tail path edge => exact ⟨_, Or.inr (BarrierPath.ancestor path), edge⟩

/-- Read the guard at any actual intermediate ancestor, not merely at a
chosen presentation of the guarded path. Functional parenthood and local
leftwardness identify it with a departure before the endpoint. -/
theorem value_at {parent : ParentMap} {value : Nat → Nat}
    {bound threshold child found z : Nat}
    (hLeft : ∀ ⦃c p⦄, c ≤ bound → parent c = some p → p < c)
    (hc : child ≤ bound) (hPath : BarrierPath parent value threshold child found)
    (hz : z = child ∨ Ancestor parent child z) (hOrder : found < z) :
    threshold ≤ value z := by
  induction child using Nat.strongRecOn generalizing found z with
  | ind child ih =>
      rcases Por.BMS.transGen_head hPath with edge | ⟨next, edge, rest⟩
      · rcases hz with rfl | hz
        · exact edge.2
        · rcases ancestor_eq_or_below_parent edge.1 hz with hEq | hRest
          · omega
          · have hFound := hLeft hc edge.1
            have := ancestor_lt_of_leftward_prefix hLeft (by omega) hRest
            omega
      · rcases hz with rfl | hz
        · exact edge.2
        · have hNext := hLeft hc edge.1
          exact ih next hNext (by omega) rest
            (ancestor_eq_or_below_parent edge.1 hz) hOrder

end BarrierPath

/-- A guard on the actual old ancestors above the endpoint equips the
actual path with a departure-by-departure barrier. -/
theorem barrierPath_of_ancestor {parent : ParentMap} {value : Nat → Nat}
    {threshold child found : Nat} (hLeft : Leftward parent)
    (hPath : Ancestor parent child found)
    (hBarrier : ∀ z, (z = child ∨ Ancestor parent child z) → found < z →
      threshold ≤ value z) :
    BarrierPath parent value threshold child found := by
  revert hBarrier
  induction hPath with
  | single edge =>
      intro hBarrier
      exact Relation.TransGen.single ⟨edge, hBarrier _ (Or.inl rfl) (hLeft edge)⟩
  | @tail middle last path edge ih =>
      intro hBarrier
      refine Relation.TransGen.tail (ih ?_) ⟨edge, hBarrier _ (Or.inr path) (hLeft edge)⟩
      intro z hz hOrder
      exact hBarrier z hz (Nat.lt_trans (hLeft edge) hOrder)

/-- One contracted edge expands to its actual candidate-forest path.
Maximality of the selected smaller ancestor proves every intermediate
barrier; the endpoint remains strictly smaller. -/
theorem nearestSmaller_barrier_path {parent : ParentMap} {value : Nat → Nat}
    {child found : Nat} (hLeft : Leftward parent)
    (hEdge : nearestSmaller parent value child = some found) :
    BarrierPath parent value (value child) child found ∧ value found < value child := by
  obtain ⟨hPath, hValue, hMax⟩ := (nearestSmaller_some_iff hLeft).mp hEdge
  refine ⟨barrierPath_of_ancestor hLeft hPath ?_, hValue⟩
  intro z hz hOrder
  rcases hz with rfl | hAncestor
  · exact Nat.le_refl _
  · by_cases hSmaller : value z < value child
    · have := hMax z hAncestor hSmaller
      omega
    · omega

/-- Expand every edge of a guarded path through one nearest-smaller event.
The result is derived by concatenating the actual old parent paths. -/
theorem barrierPath_expand_event
    {oldParent newParent : ParentMap} {value : Nat → Nat}
    {threshold bound child found : Nat} (hLeft : Leftward oldParent)
    (hNumeric : ∀ c, c ≤ bound → nearestSmaller oldParent value c = newParent c)
    (hc : child ≤ bound)
    (hPath : BarrierPath newParent value threshold child found) :
    BarrierPath oldParent value threshold child found := by
  induction hPath with
  | single edge =>
      exact ((nearestSmaller_barrier_path hLeft ((hNumeric _ hc).trans edge.1)).1).weaken
        edge.2
  | @tail middle last path edge ih =>
      have hm := ancestor_lt hLeft ih.ancestor
      have hMiddle := nearestSmaller_barrier_path hLeft
        ((hNumeric middle (by omega)).trans edge.1)
      exact ih.trans (hMiddle.1.weaken edge.2)

/-- Additive reconstruction alone gives weakly decreasing values between
successive event frontiers. No comparison or synchrony hypothesis is added. -/
theorem SynchronousBackfill.value_step_le
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish r c : Nat}
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hr : start ≤ r) (hrf : r < finish) (hc : c ≤ bound) :
    V (r + 1) c ≤ V r c := by
  classical
  by_cases hm : moves r c
  · obtain ⟨_, _, hValue⟩ := hBackfill.moving r hr hrf c hc hm
    omega
  · exact Nat.le_of_eq (hBackfill.stationary r hr hrf c hc hm).symm

/-- The weak value inequality is valid across any finite subinterval of the
backfill suffix and at any column in its fixed prefix. -/
theorem SynchronousBackfill.value_le_of_event_le
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish earlier later c : Nat}
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hStart : start ≤ earlier) (hOrder : earlier ≤ later) (hFinish : later ≤ finish)
    (hc : c ≤ bound) : V later c ≤ V earlier c := by
  induction later with
  | zero =>
      have : earlier = 0 := by omega
      subst earlier
      exact Nat.le_refl _
  | succ later ih =>
      by_cases hEq : earlier = later + 1
      · subst earlier; exact Nat.le_refl _
      · have hPrevious := ih (by omega) (by omega)
        exact Nat.le_trans (hBackfill.value_step_le (by omega) (by omega) hc) hPrevious

/-- Project a guarded path from a later designated event forest to an
earlier designated forest, keeping its fixed endpoints and threshold. -/
theorem project_event_barrier_path
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish event threshold child found : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hStart : start ≤ event) (hFinish : event ≤ finish) (hc : child ≤ bound)
    (hPath : BarrierPath (F (event + 1)) (V event) threshold child found) :
    BarrierPath (F (start + 1)) (V start) threshold child found := by
  induction event with
  | zero =>
      have : start = 0 := by omega
      subst start
      exact hPath
  | succ event ih =>
      by_cases hEq : start = event + 1
      · subst start
        exact hPath
      · have hEarlier : start ≤ event := by omega
        have hCurrentLeft : Leftward (F (event + 1)) :=
          hLeft (event + 1) (by omega) hFinish
        have hExpanded := barrierPath_expand_event hCurrentLeft
          (hNumeric (event + 1) (by omega) hFinish) hc hPath
        have hEarlierPath := hExpanded.map_values hCurrentLeft hc
          (fun c hc => hBackfill.value_step_le hEarlier (by omega) hc)
        exact ih hEarlier (by omega) hEarlierPath

/-- A later direct event parent always has an actual earlier parent path.
Every departure on that path is at least the later child's value measured
at the earlier event. The endpoint is excluded from this barrier. -/
theorem event_parent_projection
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish event child found : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hStart : start ≤ event) (hFinish : event ≤ finish) (hc : child ≤ bound)
    (hEdge : F (event + 1) child = some found) :
    BarrierPath (F (start + 1)) (V start) (V event child) child found := by
  exact project_event_barrier_path hLeft hNumeric hBackfill hStart hFinish hc
    (Relation.TransGen.single ⟨hEdge, Nat.le_refl _⟩)

/-- An additional genuine nearest-smaller expansion also projects the edge
to the candidate forest immediately before the earliest selected event. -/
theorem event_parent_projection_to_candidate
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish event child found : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hStart : start ≤ event) (hFinish : event ≤ finish) (hc : child ≤ bound)
    (hEdge : F (event + 1) child = some found) :
    BarrierPath (F start) (V start) (V event child) child found := by
  have hRange : start ≤ finish := Nat.le_trans hStart hFinish
  exact barrierPath_expand_event (hLeft start (Nat.le_refl _) hRange)
    (hNumeric start (Nat.le_refl _) hRange) hc
    (event_parent_projection hLeft hNumeric hBackfill hStart hFinish hc hEdge)

/-- Public ancestor-and-barrier form of event projection. The endpoint is
strictly left and smaller at its own event. Every earlier path vertex above
that endpoint stays within the original column prefix and blocks the later
child's value. All final-forest leftward facts are recovered from numeric
recovery in the bounded prefix; no global assumption on `F (finish+1)` is used. -/
theorem event_parent_projection_spec
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish event child found : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hStart : start ≤ event) (hFinish : event ≤ finish) (hc : child ≤ bound)
    (hEdge : F (event + 1) child = some found) :
    Ancestor (F (start + 1)) child found ∧ found < child ∧
      V event found < V event child ∧
      ∀ z, (z = child ∨ Ancestor (F (start + 1)) child z) → found < z →
        z ≤ child ∧ z ≤ bound ∧ V event child ≤ V start z := by
  have hPath := event_parent_projection hLeft hNumeric hBackfill hStart hFinish hc hEdge
  have hRange : start ≤ finish := Nat.le_trans hStart hFinish
  have hFinalLeft : ∀ ⦃c p⦄, c ≤ bound → F (start + 1) c = some p → p < c := by
    intro c p hc hParent
    exact nearestSmaller_leftward (F start) (V start)
      ((hNumeric start (Nat.le_refl _) hRange c hc).trans hParent)
  have hEndpoint := ((nearestSmaller_some_iff (hLeft event hStart hFinish)).mp
    ((hNumeric event hStart hFinish child hc).trans hEdge)).2.1
  refine ⟨hPath.ancestor, ancestor_lt_of_leftward_prefix hFinalLeft hc hPath.ancestor,
    hEndpoint, ?_⟩
  intro z hz hOrder
  have hzLe : z ≤ child := by
    rcases hz with rfl | hz
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (ancestor_lt_of_leftward_prefix hFinalLeft hc hz)
  exact ⟨hzLe, Nat.le_trans hzLe hc, hPath.value_at hFinalLeft hc hz hOrder⟩

/-- In particular, the projected chain supplies a real edge into the same
parent whose departure value still blocks the later child. -/
theorem event_parent_projected_last_edge
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish event child found : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hStart : start ≤ event) (hFinish : event ≤ finish) (hc : child ≤ bound)
    (hEdge : F (event + 1) child = some found) :
    ∃ z, (z = child ∨ Ancestor (F (start + 1)) child z) ∧
      F (start + 1) z = some found ∧ V event child ≤ V start z := by
  exact (event_parent_projection hLeft hNumeric hBackfill hStart hFinish hc hEdge).exists_last_edge

/-- If the earlier direct candidate is skipped by the later event, the
projected parent lies on that candidate's actual earlier parent chain.
The last edge into it starts at a genuine blocker on the same chain. -/
theorem event_parent_projected_candidate_blocker
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish event child candidate found : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hStart : start ≤ event) (hFinish : event ≤ finish) (hc : child ≤ bound)
    (hEdge : F (event + 1) child = some found)
    (hCandidate : F (start + 1) child = some candidate) (hDistinct : found ≠ candidate) :
    Ancestor (F (start + 1)) candidate found ∧
      ∃ z, (z = candidate ∨ Ancestor (F (start + 1)) candidate z) ∧
        F (start + 1) z = some found ∧ V event child ≤ V start z := by
  have hPath := event_parent_projection hLeft hNumeric hBackfill hStart hFinish hc hEdge
  obtain ⟨z, hZ, hLast, hBarrier⟩ := hPath.exists_last_edge
  have hCandidatePath : Ancestor (F (start + 1)) candidate found := by
    rcases ancestor_eq_or_below_parent hCandidate hPath.ancestor with hEq | hRest
    · exact (hDistinct hEq).elim
    · exact hRest
  refine ⟨hCandidatePath, z, ?_, hLast, hBarrier⟩
  rcases hZ with rfl | hZ
  · have hEq : found = candidate := Option.some.inj (hLast.symm.trans hCandidate)
    exact (hDistinct hEq).elim
  · exact ancestor_eq_or_below_parent hCandidate hZ

#print axioms nearestSmaller_barrier_path
#print axioms BarrierPath.value_at
#print axioms barrierPath_expand_event
#print axioms SynchronousBackfill.value_le_of_event_le
#print axioms project_event_barrier_path
#print axioms event_parent_projection
#print axioms event_parent_projection_to_candidate
#print axioms event_parent_projection_spec
#print axioms event_parent_projected_last_edge
#print axioms event_parent_projected_candidate_blocker

end OmegaY.Forests
