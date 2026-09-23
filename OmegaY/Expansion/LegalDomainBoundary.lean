/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/LegalDomainBoundary.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.GeneratedWellOrder

/-!
# Why legal inputs and the standard generated domain must be distinguished

The executable syntactic domain permits every positive finite sequence
starting with `1`. Its unrestricted lexicographic order is not well-founded:
`[1,2] > [1,1,2] > [1,1,1,2] > ...`. These comparisons are not asserted to
be expansion steps. Thus eventual well-foundedness of actual expansion
must be distinguished from an incorrect claim about Lex on all syntax.
-/

namespace OmegaY.Expansion.Dynamics

private def onesThenTwo (n : Nat) : Expr :=
  ⟨1 :: (List.replicate n 1 ++ [2]), Or.inr ⟨_, rfl, by
    intro value hv
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hv
    rcases hv with ⟨_, rfl⟩ | rfl <;> omega⟩⟩

private theorem onesThenTwo_descending (n : Nat) :
    Lex (onesThenTwo (n + 1)) (onesThenTwo n) := by
  change List.Lex (· < ·) (1 :: (List.replicate (n + 1) 1 ++ [2]))
    (1 :: (List.replicate n 1 ++ [2]))
  apply List.Lex.cons
  induction n with
  | zero => exact List.Lex.rel (by decide : 1 < 2)
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using List.Lex.cons ih

theorem not_wellFounded_lex_all_legal : ¬ WellFounded Lex := by
  intro hWF
  have aux : ∀ a : Expr, Acc Lex a → ∀ n, a = onesThenTwo n → False := by
    intro a hAcc
    induction hAcc with
    | intro a _ ih =>
      intro n he
      apply ih (onesThenTwo (n + 1)) ?_ (n + 1) rfl
      simpa only [he] using onesThenTwo_descending n
  exact aux _ (hWF.apply (onesThenTwo 0)) 0 rfl

end OmegaY.Expansion.Dynamics

#print axioms OmegaY.Expansion.Dynamics.not_wellFounded_lex_all_legal
