/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Forests/DepthWordWitness.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Forests.SampledDepthWords

/-!
# A strict event after a band with no reversed comparisons

A copied first-difference band can contain an earlier strict difference
than the selected effective endpoint. It suffices to rule out reversed
comparisons before that endpoint; the first actual strict event is then
the lexicographic witness. These are finite-word facts. The inequalities
at every preceding target event must still be proved from the copy rule.
-/

namespace OmegaY.Forests

open ZeroY

private theorem first_bounded_witness {predicate : Nat → Prop} {n : Nat}
    (h : predicate n) :
    ∃ first, first ≤ n ∧ predicate first ∧ ∀ earlier, earlier < first → ¬ predicate earlier := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hEarlier : ∃ earlier, earlier < n ∧ predicate earlier
    · obtain ⟨earlier, hBefore, hPredicate⟩ := hEarlier
      obtain ⟨first, hBound, hFound, hMinimal⟩ := ih earlier hBefore hPredicate
      exact ⟨first, by omega, hFound, hMinimal⟩
    · exact ⟨n, le_rfl, h, fun earlier hBefore hFound => hEarlier ⟨earlier, hBefore, hFound⟩⟩

/-- A selected strict event need not itself be the first strict event. -/
theorem depthWordLt_of_no_reverse_before_witness
    {F : Nat → ParentMap} {start finish witness left right : Nat}
    (hStart : start ≤ witness) (hFinish : witness ≤ finish)
    (hBefore : ∀ event, start ≤ event → event < witness →
      eventDepth F event left ≤ eventDepth F event right)
    (hStrict : eventDepth F witness left < eventDepth F witness right) :
    DepthWordLt F start finish left right := by
  classical
  obtain ⟨first, hFirstBound, ⟨hFirstStart, hFirstStrict⟩, hMinimal⟩ :=
    first_bounded_witness
      (predicate := fun event => start ≤ event ∧ eventDepth F event left < eventDepth F event right)
      (n := witness) ⟨hStart, hStrict⟩
  refine ⟨first, hFirstStart, hFirstBound.trans hFinish, ?_, hFirstStrict⟩
  intro event hEvent hEarlier
  have hLe := hBefore event hEvent (hEarlier.trans_le hFirstBound)
  have hNotStrict : ¬ eventDepth F event left < eventDepth F event right :=
    fun h => hMinimal event hEarlier ⟨hEvent, h⟩
  exact Nat.le_antisymm hLe (Nat.le_of_not_gt hNotStrict)

/-- Combine complete equality before the split band, no reversal in its
interior, and a strict effective endpoint. No event is omitted. -/
theorem depthWordLt_of_equal_prefix_le_band
    {F : Nat → ParentMap} {start finish bandStart witness left right : Nat}
    (hStart : start ≤ witness) (hFinish : witness ≤ finish)
    (hPrefix : ∀ event, start ≤ event → event < bandStart →
      eventDepth F event left = eventDepth F event right)
    (hBand : ∀ event, start ≤ event → bandStart ≤ event → event < witness →
      eventDepth F event left ≤ eventDepth F event right)
    (hStrict : eventDepth F witness left < eventDepth F witness right) :
    DepthWordLt F start finish left right := by
  apply depthWordLt_of_no_reverse_before_witness hStart hFinish ?_ hStrict
  intro event hEvent hBefore
  by_cases hLow : event < bandStart
  · exact (hPrefix event hEvent hLow).le
  · exact hBand event hEvent (Nat.le_of_not_gt hLow) hBefore

end OmegaY.Forests

#print axioms OmegaY.Forests.depthWordLt_of_no_reverse_before_witness
#print axioms OmegaY.Forests.depthWordLt_of_equal_prefix_le_band
