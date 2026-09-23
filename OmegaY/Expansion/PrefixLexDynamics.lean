/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PrefixLexDynamics.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PrefixDynamics
import Mathlib.Data.List.Lex

/-!
# Actual first change, lexicographic descent, and the seed step

Positive copying preserves the entire decremented source as a prefix.
Thus the first changed value is the old last value, decreased by one;
the deletion branches are proper prefixes. This is one-step strict Lex
descent, not well-foundedness of Lex on all legal strings.
-/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem lex_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl

theorem Preparation.decremented_prefix_of_expand {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : List Nat} (hRun : expand (front ++ [last]) copies = .ok result) :
    List.IsPrefix (front ++ [last - 1]) result := by
  obtain ⟨diagram, hDiagram, hValid⟩ := OmegaY.Expansion.expandDiagram_total
    (build_success_legal p.initial_build) copies
  have hValues : valuesOf diagram = .ok result := by simpa only [expand, hDiagram, lex_bind_ok] using hRun
  have he : bottomValues diagram = result := Except.ok.inj
    ((valuesOf_eq_bottomValues hValid).symm.trans hValues)
  have hPrefix := (p.expandDiagram_reduced_preserved hLast hCopies hDiagram).bottomValues_prefix
  simpa only [bottomValues_of_build p.reduced_build, he] using hPrefix

theorem Preparation.expand_length {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : List Nat} (hRun : expand (front ++ [last]) copies = .ok result) :
    result.length = front.length + copies * (front.length - p.root.column) := by
  obtain ⟨full, hFull, ready⟩ := p.blocks_total hLast copies
  have hValues : expand (front ++ [last]) copies = .ok (bottomValues full.pop) := by
    simpa only [expand, p.expandDiagram_of_blocks hLast hCopies hFull, lex_bind_ok] using
      valuesOf_eq_bottomValues ready.valid.pop
  have he : result = bottomValues full.pop := Except.ok.inj (hRun.symm.trans hValues)
  rw [he, bottomValues_length, Array.size_pop]
  have hSourceSize := build_size p.reduced_build
  simp only [List.length_append, List.length_singleton] at hSourceSize
  have hSize := ready.size_eq
  rw [hSourceSize, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul] at hSize
  have hRoot := p.root_before_last
  omega

theorem Preparation.expand_lex_lt_positive {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : List Nat} (hRun : expand (front ++ [last]) copies = .ok result) :
    List.Lex (· < ·) result (front ++ [last]) := by
  obtain ⟨tail, hTail⟩ := p.decremented_prefix_of_expand hLast hCopies hRun
  rw [← hTail, List.append_assoc]
  exact List.Lex.append_left (· < ·) (List.Lex.rel (show last - 1 < last by omega)) front

private theorem delete_last_lex_lt {values : List Nat} (hNonempty : values ≠ []) :
    List.Lex (· < ·) (values.take (values.length - 1)) values := by
  rcases List.eq_nil_or_concat' values with hNil | ⟨front, last, rfl⟩
  · exact (hNonempty hNil).elim
  · simpa using List.Lex.append_left (· < ·) (List.Lex.nil (a := last) (l := [])) front

theorem expand_lex_lt {values result : List Nat} (hLegal : Legal values)
    (hNonempty : values ≠ []) {copies : Nat} (hRun : expand values copies = .ok result) :
    List.Lex (· < ·) result values := by
  by_cases hTrivial : values = [] ∨ values.getLast? = some 1 ∨ copies = 0
  · have he : result = values.take (values.length - 1) := Except.ok.inj
      (hRun.symm.trans (expand_delete_of_trivial hLegal copies hTrivial))
    exact he ▸ delete_last_lex_lt hNonempty
  · rcases hLegal with rfl | ⟨rest, rfl, hPositive⟩
    · exact (hNonempty rfl).elim
    · rcases List.eq_nil_or_concat' rest with rfl | ⟨middle, last, rfl⟩
      · exact (hTrivial (Or.inr (Or.inl rfl))).elim
      · have hLastPositive : 0 < last := hPositive last (by simp)
        have hLastNe : last ≠ 1 := by
          intro h
          apply hTrivial
          right; left
          change ((1 :: middle) ++ [last]).getLast? = some 1
          rw [List.getLast?_append]
          simp [h]
        have hLast : 1 < last := by omega
        have hCopies : 0 < copies := by
          by_contra hn
          exact hTrivial (Or.inr (Or.inr (by omega)))
        obtain ⟨p⟩ := preparation_total middle last
          (fun value hv => hPositive value (by simp [hv])) hLast
        exact p.expand_lex_lt_positive hLast hCopies hRun

theorem expand_seed_one (m : Nat) (hm : 0 < m) :
    expand [1, m + 1] 1 = .ok [1, m] := by
  obtain ⟨p⟩ := preparation_total [] (m + 1) (by simp) (by omega)
  obtain ⟨result, hRun, _⟩ := expand_total (build_success_legal p.initial_build) 1
  have hRoot : p.root.column = 0 := by have h := p.root_before_last; simp only [List.length_cons, List.length_nil] at h; omega
  have hLength := p.expand_length (by omega) (by omega) hRun
  simp only [List.length_cons, List.length_nil, hRoot, Nat.sub_zero, Nat.one_mul] at hLength
  have hPrefix := p.decremented_prefix_of_expand (by omega) (by omega) hRun
  have he : [1, m] = result := hPrefix.eq_of_length (by simpa using hLength.symm)
  simpa only [List.nil_append, List.cons_append, Nat.add_sub_cancel, ← he] using hRun

end OmegaY.Expansion

#print axioms OmegaY.Expansion.Preparation.decremented_prefix_of_expand
#print axioms OmegaY.Expansion.Preparation.expand_length
#print axioms OmegaY.Expansion.Preparation.expand_lex_lt_positive
#print axioms OmegaY.Expansion.expand_lex_lt
#print axioms OmegaY.Expansion.expand_seed_one
