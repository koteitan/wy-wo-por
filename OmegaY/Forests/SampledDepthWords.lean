/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Forests/SampledDepthWords.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Forests.DepthValues
import Mathlib.Order.Hom.Basic

/-!
# Finite event subdivision and common root-depth corrections

A monotone surjective sampling of two finite event intervals may repeat a
source event. Crossed-sum depth identities with an ordered root-membership
correction preserve equality and the first strict difference. This handles
finite event subdivision without deleting unexamined target events.

This is a structural transport lemma. Constructing such samplings and depth
identities from actual copied root intervals is a separate obligation.
-/

namespace OmegaY.Forests

open ZeroY

structure EventSampling (sourceStart sourceFinish targetStart targetFinish : Nat) where
  sample : Nat → Nat
  bounds : ∀ t, targetStart ≤ t → t ≤ targetFinish →
    sourceStart ≤ sample t ∧ sample t ≤ sourceFinish
  monotone : ∀ a b, targetStart ≤ a → a ≤ b → b ≤ targetFinish → sample a ≤ sample b
  covers : ∀ s, sourceStart ≤ s → s ≤ sourceFinish →
    ∃ t, targetStart ≤ t ∧ t ≤ targetFinish ∧ sample t = s

private theorem first_finite_witness {predicate : Nat → Prop} {n : Nat} (h : predicate n) :
    ∃ first, first ≤ n ∧ predicate first ∧ ∀ earlier, earlier < first → ¬ predicate earlier := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hEarlier : ∃ earlier, earlier < n ∧ predicate earlier
    · obtain ⟨earlier, hBefore, hPredicate⟩ := hEarlier
      obtain ⟨first, hFirst, hFound, hMinimal⟩ := ih earlier hBefore hPredicate
      exact ⟨first, by omega, hFound, hMinimal⟩
    · exact ⟨n, le_rfl, h, fun earlier hBefore hPredicate => hEarlier ⟨earlier, hBefore, hPredicate⟩⟩

/-- Every source event has a first actual occurrence, and all earlier
target events sample strictly earlier source events. -/
theorem EventSampling.first_occurrence {sourceStart sourceFinish targetStart targetFinish : Nat}
    (sampling : EventSampling sourceStart sourceFinish targetStart targetFinish)
    {sourceEvent : Nat} (hStart : sourceStart ≤ sourceEvent) (hFinish : sourceEvent ≤ sourceFinish) :
    ∃ targetEvent, targetStart ≤ targetEvent ∧ targetEvent ≤ targetFinish ∧
      sampling.sample targetEvent = sourceEvent ∧
      ∀ earlier, targetStart ≤ earlier → earlier < targetEvent → sampling.sample earlier < sourceEvent := by
  classical
  obtain ⟨someEvent, hSome⟩ := sampling.covers sourceEvent hStart hFinish
  obtain ⟨targetEvent, _, hSpec, hMinimal⟩ := first_finite_witness
    (predicate := fun t => targetStart ≤ t ∧ t ≤ targetFinish ∧ sampling.sample t = sourceEvent)
    (n := someEvent) hSome
  refine ⟨targetEvent, hSpec.1, hSpec.2.1, hSpec.2.2, ?_⟩
  intro earlier hEarlier hBefore
  have hLe : sampling.sample earlier ≤ sourceEvent :=
    (sampling.monotone earlier targetEvent hEarlier hBefore.le hSpec.2.1).trans_eq hSpec.2.2
  have hNe : sampling.sample earlier ≠ sourceEvent := by
    intro he
    exact hMinimal earlier hBefore ⟨hEarlier, hBefore.le.trans hSpec.2.1, he⟩
  exact lt_of_le_of_ne hLe hNe

/-- The common baseline may vary from event to event. Corrections may also
vary between columns, but equality and strict order of source depths must
respect their root-membership coefficients. No word-order conclusion is
assumed in these local structural fields. -/
structure SampledDepthCorrection (source target : Nat → ParentMap)
    {sourceStart sourceFinish targetStart targetFinish : Nat}
    (sampling : EventSampling sourceStart sourceFinish targetStart targetFinish)
    (sourceLeft sourceRight targetLeft targetRight : Nat) where
  baseline : Nat → Nat
  extra : Nat → Nat
  leftCoefficient : Nat → Nat
  rightCoefficient : Nat → Nat
  left_balance : ∀ t, targetStart ≤ t → t ≤ targetFinish →
    eventDepth target t targetLeft + baseline t =
      eventDepth source (sampling.sample t) sourceLeft + leftCoefficient t * extra t
  right_balance : ∀ t, targetStart ≤ t → t ≤ targetFinish →
    eventDepth target t targetRight + baseline t =
      eventDepth source (sampling.sample t) sourceRight + rightCoefficient t * extra t
  equal_coefficients : ∀ t, targetStart ≤ t → t ≤ targetFinish →
    eventDepth source (sampling.sample t) sourceLeft = eventDepth source (sampling.sample t) sourceRight →
      leftCoefficient t = rightCoefficient t
  ordered_coefficients : ∀ t, targetStart ≤ t → t ≤ targetFinish →
    eventDepth source (sampling.sample t) sourceLeft < eventDepth source (sampling.sample t) sourceRight →
      leftCoefficient t ≤ rightCoefficient t

namespace SampledDepthCorrection

variable {source target : Nat → ParentMap}
  {sourceStart sourceFinish targetStart targetFinish : Nat}
  {sampling : EventSampling sourceStart sourceFinish targetStart targetFinish}
  {sourceLeft sourceRight targetLeft targetRight : Nat}
  (correction : SampledDepthCorrection source target sampling sourceLeft sourceRight targetLeft targetRight)

include correction

theorem equal_at {event : Nat} (hStart : targetStart ≤ event) (hFinish : event ≤ targetFinish)
    (hEq : eventDepth source (sampling.sample event) sourceLeft =
      eventDepth source (sampling.sample event) sourceRight) :
    eventDepth target event targetLeft = eventDepth target event targetRight := by
  have hL := correction.left_balance event hStart hFinish
  have hR := correction.right_balance event hStart hFinish
  have hCoefficient := correction.equal_coefficients event hStart hFinish hEq
  rw [hCoefficient] at hL
  omega

theorem less_at {event : Nat} (hStart : targetStart ≤ event) (hFinish : event ≤ targetFinish)
    (hLt : eventDepth source (sampling.sample event) sourceLeft <
      eventDepth source (sampling.sample event) sourceRight) :
    eventDepth target event targetLeft < eventDepth target event targetRight := by
  have hL := correction.left_balance event hStart hFinish
  have hR := correction.right_balance event hStart hFinish
  have hCoefficient := correction.ordered_coefficients event hStart hFinish hLt
  have hProduct := Nat.mul_le_mul_right (correction.extra event) hCoefficient
  omega

theorem word_eq (hWord : DepthWordEq source sourceStart sourceFinish sourceLeft sourceRight) :
    DepthWordEq target targetStart targetFinish targetLeft targetRight := by
  intro event hStart hFinish
  have hBounds := sampling.bounds event hStart hFinish
  exact correction.equal_at hStart hFinish (hWord _ hBounds.1 hBounds.2)

theorem word_lt (hWord : DepthWordLt source sourceStart sourceFinish sourceLeft sourceRight) :
    DepthWordLt target targetStart targetFinish targetLeft targetRight := by
  obtain ⟨event, hStart, hFinish, hBefore, hLess⟩ := hWord
  obtain ⟨targetEvent, htStart, htFinish, htSame, htBefore⟩ := sampling.first_occurrence hStart hFinish
  refine ⟨targetEvent, htStart, htFinish, ?_, ?_⟩
  · intro earlier hEarlier hEarlierLt
    have hEarlierFinish := hEarlierLt.le.trans htFinish
    have hBounds := sampling.bounds earlier hEarlier hEarlierFinish
    exact correction.equal_at hEarlier hEarlierFinish
      (hBefore _ hBounds.1 (htBefore earlier hEarlier hEarlierLt))
  · exact correction.less_at htStart htFinish (by simpa only [htSame] using hLess)

theorem word_le (hWord : DepthWordLe source sourceStart sourceFinish sourceLeft sourceRight) :
    DepthWordLe target targetStart targetFinish targetLeft targetRight :=
  hWord.elim (fun h => Or.inl (correction.word_eq h)) (fun h => Or.inr (correction.word_lt h))

end SampledDepthCorrection
end OmegaY.Forests

#print axioms OmegaY.Forests.EventSampling.first_occurrence
#print axioms OmegaY.Forests.SampledDepthCorrection.equal_at
#print axioms OmegaY.Forests.SampledDepthCorrection.less_at
#print axioms OmegaY.Forests.SampledDepthCorrection.word_eq
#print axioms OmegaY.Forests.SampledDepthCorrection.word_lt
#print axioms OmegaY.Forests.SampledDepthCorrection.word_le
