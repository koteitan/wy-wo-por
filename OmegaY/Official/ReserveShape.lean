import OmegaY.Official.Reserve
import OmegaY.Canonical.Domain

/-!
# The shape of the leg atoms

Every leg atom of a valid mountain is well formed (`Reserve.wellFormed`): its parent
column is left of its child column, its child is a column of the mountain, its key
has `D + 1` entries, and every column entry of the key is at most the parent.
Canonical mountains are valid (`Canonical.build_valid_of_success`), so this holds
for the mountain of every legal sequence.
-/

namespace OmegaY.Official.Reserve

open Canonical

theorem scaleRoot_column_le (M : Mountain) (k : Nat) :
    ∀ (fuel : Nat) (r : Ref), (scaleRoot M k fuel r).column ≤ r.column := by
  intro fuel
  induction fuel with
  | zero => intro r; simp [scaleRoot]
  | succ fuel ih =>
      intro r
      simp only [scaleRoot]
      split
      · rename_i p c _ _
        split
        · rename_i cp _
          split
          · rename_i h
            exact le_trans (ih p) (le_of_lt h.2)
          · exact le_refl _
        · exact le_refl _
      · exact le_refl _

theorem keyAt_length {M : Mountain} {D : Nat} {row : Row} {p : Ref} {cp : Cell}
    (h : cell? M p = some cp) : (keyAt M D row p).length = D + 1 := by
  simp [keyAt, h]

theorem keyAt_entry {M : Mountain} {D : Nat} {row : Row} {p : Ref} {v : Nat}
    (h : some v ∈ keyAt M D row p) : v ≤ p.column := by
  unfold keyAt at h
  split at h
  · simp at h
  · simp only [List.mem_map, List.mem_reverse, List.mem_range] at h
    obtain ⟨k, _, hk⟩ := h
    split at hk
    · simp only [Option.some.injEq] at hk
      rw [← hk]
      exact scaleRoot_column_le M k _ p
    · simp at hk

theorem highestAtMost_cell {M : Mountain} {l : Nat} {row : Row} {p : Ref}
    (h : highestAtMost M l row = some p) : p.column = l ∧ ∃ cp, cell? M p = some cp := by
  simp only [highestAtMost, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨col, hcol, j, hj, hp⟩ := h
  subst hp
  refine ⟨rfl, ?_⟩
  have hmem := List.mem_of_getLast? hj
  rw [List.mem_filter, List.mem_range] at hmem
  obtain ⟨hjs, _⟩ := hmem
  exact ⟨col[j], by simp [cell?, hcol, hjs]⟩

/-- Every leg atom of a valid mountain is well formed. -/
theorem atoms_wellFormed {M : Mountain} (hV : MountainValid M) (D : Nat) :
    ∀ a ∈ atoms M D, wellFormed D M.size a = true := by
  intro a ha
  simp only [atoms, List.mem_flatMap, List.mem_range] at ha
  obtain ⟨c, hc, ha⟩ := ha
  split at ha
  · simp at ha
  · rename_i hc0
    cases hcol : M[c]? with
    | none => simp [hcol] at ha
    | some col =>
        simp only [hcol, List.mem_filterMap, List.mem_range] at ha
        obtain ⟨i, hi, hsome⟩ := ha
        split at hsome
        · simp at hsome
        · rename_i hi0
          have hcolEq : M[c] = col := by
            have := hcol; rw [Array.getElem?_eq_getElem hc] at this; exact Option.some.inj this
          have hCV := hV c hc
          rw [hcolEq] at hCV
          unfold legAtom? at hsome
          simp only [Option.bind_eq_bind] at hsome
          cases hcu : cell? M ⟨c, i⟩ with
          | none => simp [hcu] at hsome
          | some cu =>
              simp only [hcu, Option.bind_some] at hsome
              have hcu' : col[i]? = some cu := by simpa [cell?, hcol] using hcu
              cases hl : cu.left with
              | none => simp [hl] at hsome
              | some l =>
                  simp only [hl, Option.bind_some] at hsome
                  cases hp : highestAtMost M l.column cu.row with
                  | none => simp [hp] at hsome
                  | some p =>
                      simp only [hp, Option.bind_some, Option.pure_def, Option.some.injEq] at hsome
                      subst hsome
                      obtain ⟨hlc, _⟩ := hCV.stored_valid i cu l hcu' hl
                      obtain ⟨hpl, cp, hcp⟩ := highestAtMost_cell hp
                      simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
                      refine ⟨⟨⟨hlc, hc⟩, keyAt_length hcp⟩, ?_⟩
                      intro e he
                      cases e with
                      | none => rfl
                      | some v =>
                          have := keyAt_entry he
                          simp only [decide_eq_true_eq]
                          omega

end OmegaY.Official.Reserve
