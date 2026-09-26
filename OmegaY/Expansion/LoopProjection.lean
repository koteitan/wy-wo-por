/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/LoopProjection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.LoopInvariant

/-! Exact list projections of actual non-breaking finite loops. -/

namespace OmegaY.Expansion

theorem forIn_append_projection {α β γ : Type} (xs : List α) (initial : β)
    (body : α → β → Result (ForInStep β)) (invariant : β → Prop)
    (project : β → List γ) (additions : α → List γ) (hinit : invariant initial)
    (hbody : ∀ item ∈ xs, ∀ state, invariant state →
      ∃ next, body item state = .ok (.yield next) ∧ invariant next ∧
        project next = project state ++ additions item) :
    ∃ result, (forIn xs initial body : Result β) = .ok result ∧ invariant result ∧
      project result = project initial ++ xs.flatMap additions := by
  induction xs generalizing initial with
  | nil => exact ⟨initial, rfl, hinit, by simp⟩
  | cons item rest ih =>
    obtain ⟨next, hn, hi, hp⟩ := hbody item (by simp) initial hinit
    obtain ⟨result, hr, hinv, hproject⟩ := ih next hi
      (fun a ha state hs => hbody a (by simp [ha]) state hs)
    refine ⟨result, ?_, hinv, ?_⟩
    · rw [List.forIn_cons, hn]
      exact hr
    · simpa only [List.flatMap_cons, List.append_assoc, hp] using hproject

theorem returns_forIn_projection {α β γ : Type} (xs : List α) (initial : β)
    (body : α → β → Result (ForInStep β)) (invariant : β → Prop)
    (project : β → List γ) (additions : α → List γ) (hinit : invariant initial)
    (hbody : ∀ item ∈ xs, ∀ state, invariant state →
      ∃ next, body item state = .ok (.yield next) ∧ invariant next ∧
        project next = project state ++ additions item) :
    Returns (forIn xs initial body : Result β)
      (fun result => invariant result ∧ project result = project initial ++ xs.flatMap additions) :=
  forIn_append_projection xs initial body invariant project additions hinit hbody

theorem forIn_yield_projection {α β γ : Type} (xs : List α) (initial : β)
    (body : α → β → Result (ForInStep β)) (invariant : β → Prop)
    (project : β → List γ) (additions : α → List γ) (final : List γ)
    (hinit : invariant initial) (hfinal : xs.flatMap additions = final)
    (hbody : ∀ item ∈ xs, ∀ state, invariant state →
      ∃ next, body item state = .ok (.yield next) ∧ invariant next ∧
        project next = project state ++ additions item) :
    ∃ result,
      (do let output ← forIn xs initial body; pure (.yield output) : Result (ForInStep β)) =
        .ok (.yield result) ∧ invariant result ∧ project result = project initial ++ final := by
  obtain ⟨result, hr, hi, hp⟩ :=
    forIn_append_projection xs initial body invariant project additions hinit hbody
  refine ⟨result, ?_, hi, by simpa only [hfinal] using hp⟩
  rw [hr]
  rfl

end OmegaY.Expansion
