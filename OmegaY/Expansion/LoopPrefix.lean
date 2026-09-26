/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/LoopPrefix.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.IndexedLoop

/-! Actual execution prefixes for finite loops whose successful body
always yields. Errors remain errors; no totality is assumed of the body. -/

namespace OmegaY.Expansion

theorem forIn_bind_yield_eq_foldlM {Item State : Type} (items : List Item)
    (initial : State) (step : Item → State → Result State) :
    (forIn items initial (fun item state => do
      let next ← step item state
      pure (.yield next)) : Result State) =
        items.foldlM (fun state item => step item state) initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
    rw [List.forIn_cons, List.foldlM_cons]
    cases hStep : step item initial with
    | error error => rfl
    | ok next => exact ih next

/-- One more successful yield extends the actual range-loop execution. -/
theorem forIn_yield_range_succ {State : Type} (initial : State)
    (step : Nat → State → Result State) {count : Nat} {before after : State}
    (hRun : (forIn (List.range count) initial (fun index state => do
      let next ← step index state
      pure (.yield next)) : Result State) = .ok before)
    (hStep : step count before = .ok after) :
    (forIn (List.range (count + 1)) initial (fun index state => do
      let next ← step index state
      pure (.yield next)) : Result State) = .ok after := by
  have hFold : (List.range count).foldlM (fun state index => step index state) initial =
      .ok before := (forIn_bind_yield_eq_foldlM (List.range count) initial step).symm.trans hRun
  rw [forIn_bind_yield_eq_foldlM, List.range_succ, List.foldlM_append, hFold]
  change step count before >>= (fun state => pure state) = .ok after
  rw [hStep]
  rfl

end OmegaY.Expansion

#print axioms OmegaY.Expansion.forIn_bind_yield_eq_foldlM
#print axioms OmegaY.Expansion.forIn_yield_range_succ
