/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/LoopInvariant.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.LoopTotality

/-! Invariants for the actual `Except`/`forIn` loops. -/

namespace OmegaY.Expansion

def Returns {α : Type} (action : Result α) (post : α → Prop) : Prop :=
  ∃ value, action = .ok value ∧ post value

theorem returns_pure {α : Type} {post : α → Prop} {value : α} (h : post value) :
    Returns (pure value : Result α) post := ⟨value, rfl, h⟩

theorem returns_bind {α β : Type} {action : Result α} {next : α → Result β}
    {post : α → Prop} {final : β → Prop}
    (h : Returns action post) (hn : ∀ value, post value → Returns (next value) final) :
    Returns (action >>= next) final := by
  obtain ⟨value, hv, hp⟩ := h
  rw [hv]
  exact hn value hp

def StepInvariant {α : Type} (post : α → Prop) : ForInStep α → Prop
  | .done value => post value
  | .yield value => post value

theorem returns_forIn {α β : Type} (xs : List α) (initial : β)
    (body : α → β → Result (ForInStep β)) (post : β → Prop) (hinit : post initial)
    (hbody : ∀ item ∈ xs, ∀ state, post state → Returns (body item state) (StepInvariant post)) :
    Returns (forIn xs initial body : Result β) post := by
  induction xs generalizing initial with
  | nil => exact ⟨initial, rfl, hinit⟩
  | cons item rest ih =>
    obtain ⟨step, hs, hp⟩ := hbody item (by simp) initial hinit
    rw [List.forIn_cons, hs]
    cases step with
    | done state => exact ⟨state, rfl, hp⟩
    | yield state =>
      exact ih state hp (fun item hi state hstate => hbody item (by simp [hi]) state hstate)

end OmegaY.Expansion

#print axioms OmegaY.Expansion.returns_forIn
