/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/LegalDynamics.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.PrefixLexDynamics

/-!
# Actual expansion dynamics on all legal finite sequences

`next` is the successful output of the unchanged executable expansion.
Its totality, legality, zero-copy deletion, nested prefixes and strict
lexicographic descent are theorems about that implementation. `Step`
excludes the empty input, whose total expansion would otherwise be a
self-loop. Nothing in this file asserts well-foundedness of `Step`.
-/

namespace OmegaY.Expansion.Dynamics

abbrev Expr := { values : List Nat // Canonical.Legal values }

/-- The actual total expansion, with legality packaged in its result. -/
noncomputable def next (s : Expr) (copies : Nat) : Expr :=
  let h := expand_total s.property copies
  ⟨Classical.choose h, (Classical.choose_spec h).2⟩

theorem next_run (s : Expr) (copies : Nat) :
    expand s.val copies = .ok (next s copies).val :=
  (Classical.choose_spec (expand_total s.property copies)).1

theorem next_eq_of_run {s : Expr} {copies : Nat} {values : List Nat}
    (hRun : expand s.val copies = .ok values) : (next s copies).val = values :=
  Except.ok.inj ((next_run s copies).symm.trans hRun)

theorem next_zero (s : Expr) :
    (next s 0).val = s.val.take (s.val.length - 1) :=
  next_eq_of_run (expand_zero s.property)

theorem next_empty {s : Expr} (hEmpty : s.val = []) (copies : Nat) : next s copies = s := by
  apply Subtype.ext
  have h := next_eq_of_run (expand_delete_of_trivial s.property copies (Or.inl hEmpty))
  simpa only [hEmpty, List.length_nil, Nat.zero_sub, List.take_nil] using h

/-- Child-to-parent orientation, as required by `WellFounded`. -/
def Step (child parent : Expr) : Prop :=
  parent.val ≠ [] ∧ ∃ copies, next parent copies = child

abbrev Desc := Relation.TransGen Step

def Lex (a b : Expr) : Prop := List.Lex (· < ·) a.val b.val

theorem next_lex {s : Expr} (hNonempty : s.val ≠ []) (copies : Nat) :
    Lex (next s copies) s :=
  expand_lex_lt s.property hNonempty (next_run s copies)

theorem step_lex {a b : Expr} (h : Step a b) : Lex a b := by
  obtain ⟨hNonempty, copies, rfl⟩ := h
  exact next_lex hNonempty copies

theorem lex_trans {a b c : Expr} (h : Lex a b) (g : Lex b c) : Lex a c := by
  exact lt_trans (show a.val < b.val from h) (show b.val < c.val from g)

theorem lex_asymm {a b : Expr} (h : Lex a b) (g : Lex b a) : False := by
  exact lt_asymm (show a.val < b.val from h) (show b.val < a.val from g)

theorem lex_trichotomy (a b : Expr) : Lex a b ∨ a = b ∨ Lex b a := by
  rcases lt_trichotomy a.val b.val with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr h)

theorem step_ne {a b : Expr} (h : Step a b) : a ≠ b := by
  intro he
  subst b
  exact lex_asymm (step_lex h) (step_lex h)

theorem step_iff_nontrivial (a b : Expr) :
    Step a b ↔ (∃ copies, next b copies = a) ∧ a ≠ b := by
  constructor
  · intro h
    exact ⟨h.2, step_ne h⟩
  · rintro ⟨⟨copies, hCopy⟩, hNe⟩
    refine ⟨?_, copies, hCopy⟩
    intro hEmpty
    exact hNe (hCopy.symm.trans (next_empty hEmpty copies))

theorem no_step_from_empty {s t : Expr} (hEmpty : s.val = []) : ¬ Step t s :=
  fun h => h.1 hEmpty

/-- Forward finite execution, including zero steps but no empty self-loop. -/
inductive Path : Expr → Expr → Prop
  | refl (s : Expr) : Path s s
  | tail {root middle : Expr} (prior : Path root middle) (copies : Nat)
      (hNonempty : middle.val ≠ []) : Path root (next middle copies)

namespace Path

theorem single (s : Expr) (copies : Nat) : Path s (next s copies) := by
  by_cases h : s.val = []
  · rw [next_empty h]
    exact .refl _
  · exact .tail (.refl _) copies h

theorem of_step {a b : Expr} (h : Step b a) : Path a b := by
  obtain ⟨hn, copies, rfl⟩ := h
  exact .tail (.refl _) copies hn

theorem trans {a b c : Expr} (h : Path a b) (g : Path b c) : Path a c := by
  induction g with
  | refl => exact h
  | tail prior copies hn ih => exact .tail ih copies hn

theorem eq_or_desc {s t : Expr} (h : Path s t) : t = s ∨ Desc t s := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail middle prior copies hn ih =>
    have hs : Step (next middle copies) middle := ⟨hn, copies, rfl⟩
    rcases ih with he | hd
    · subst middle
      exact Or.inr (.single hs)
    · exact Or.inr ((Relation.TransGen.single hs).trans hd)

theorem eq_or_first_step {s t : Expr} (h : Path s t) :
    t = s ∨ ∃ first, Step first s ∧ Path first t := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail middle prior copies hn ih =>
    rcases ih with he | ⟨first, hf, hr⟩
    · subst middle
      exact Or.inr ⟨next s copies, ⟨hn, copies, rfl⟩, .refl _⟩
    · exact Or.inr ⟨first, hf, .tail hr copies hn⟩

theorem of_desc {s t : Expr} (h : Desc t s) : Path s t := by
  induction h with
  | single h => exact of_step h
  | tail prior h ih => exact (of_step h).trans ih

theorem iff_eq_or_desc (s t : Expr) : Path s t ↔ t = s ∨ Desc t s := by
  constructor
  · exact eq_or_desc
  · rintro (rfl | h)
    · exact .refl _
    · exact of_desc h

theorem acc {s t : Expr} (h : Path s t) (hs : Acc Step s) : Acc Step t := by
  rcases h.eq_or_desc with rfl | hd
  · exact hs
  · exact hs.inv_of_transGen hd

end Path

theorem desc_lex {a b : Expr} (h : Desc a b) : Lex a b := by
  induction h with
  | single h => exact step_lex h
  | tail prior h ih => exact lex_trans ih (step_lex h)

theorem legal_take {values : List Nat} (hLegal : Canonical.Legal values) (n : Nat) :
    Canonical.Legal (values.take n) := by
  rcases hLegal with rfl | ⟨rest, rfl, hPositive⟩
  · exact Or.inl (by simp)
  · cases n with
    | zero => exact Or.inl rfl
    | succ n =>
      refine Or.inr ⟨rest.take n, rfl, ?_⟩
      intro value hv
      exact hPositive value (List.mem_of_mem_take hv)

def take (s : Expr) (n : Nat) : Expr := ⟨s.val.take n, legal_take s.property n⟩

theorem path_take (s : Expr) (n : Nat) : Path s (take s n) := by
  have aux : ∀ m, ∀ t : Expr, t.val.length = m → Path t (take t n) := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro t hm
      by_cases hn : t.val.length ≤ n
      · have he : take t n = t := Subtype.ext (List.take_of_length_le hn)
        rw [he]
        exact .refl _
      · have hLen : (next t 0).val.length = t.val.length - 1 := by
          rw [next_zero]
          simp only [List.length_take, Nat.min_eq_left (Nat.sub_le _ _)]
        have hNext := ih (next t 0).val.length (by omega) (next t 0) rfl
        have he : take (next t 0) n = take t n := by
          apply Subtype.ext
          change (next t 0).val.take n = t.val.take n
          rw [next_zero, List.take_take, Nat.min_eq_left (by omega : n ≤ t.val.length - 1)]
        rw [he] at hNext
        exact (Path.single t 0).trans hNext
  exact aux s.val.length s rfl

theorem next_prefix (s : Expr) {i j : Nat} (hOrder : i ≤ j) :
    List.IsPrefix (next s i).val (next s j).val :=
  expand_prefix s.property hOrder (next_run s i) (next_run s j)

/-- Every earlier copy-count branch is reachable from every later branch. -/
theorem earlier_branch (s : Expr) {i j : Nat} (hOrder : i ≤ j) :
    Path (next s j) (next s i) := by
  have hTake : take (next s j) (next s i).val.length = next s i :=
    Subtype.ext (List.prefix_iff_eq_take.mp (next_prefix s hOrder)).symm
  rw [← hTake]
  exact path_take _ _

/-- The standard seeds are exactly `[1,n]` with `n ≥ 2`. -/
def seed (n : Nat) : Expr :=
  ⟨[1, n + 2], Or.inr ⟨[n + 2], rfl, by simp⟩⟩

theorem seed_nonempty (n : Nat) : (seed n).val ≠ [] := by simp [seed]

theorem seed_step (n : Nat) : next (seed (n + 1)) 1 = seed n := by
  apply Subtype.ext
  exact next_eq_of_run (by simpa [seed, Nat.add_assoc] using expand_seed_one (n + 2) (by omega))

theorem seed_path (i j : Nat) (hOrder : i ≤ j) : Path (seed j) (seed i) := by
  induction j with
  | zero =>
    have he : i = 0 := by omega
    subst i
    exact .refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i
      exact .refl _
    · have hFirst := Path.single (seed (j + 1)) 1
      rw [seed_step] at hFirst
      exact hFirst.trans (ih (by omega))

def Generated (s : Expr) : Prop := ∃ n, Path (seed n) s

abbrev GeneratedExpr := { s : Expr // Generated s }
abbrev Descendant (root : Expr) := { s : Expr // Path root s }

theorem generated_seed (n : Nat) : Generated (seed n) := ⟨n, .refl _⟩

theorem Generated.next {s : Expr} (h : Generated s) (copies : Nat) :
    Generated (next s copies) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.trans (Path.single s copies)⟩

theorem Generated.take {s : Expr} (h : Generated s) (n : Nat) : Generated (take s n) := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk.trans (path_take s n)⟩

end OmegaY.Expansion.Dynamics

#print axioms OmegaY.Expansion.Dynamics.next_run
#print axioms OmegaY.Expansion.Dynamics.step_iff_nontrivial
#print axioms OmegaY.Expansion.Dynamics.path_take
#print axioms OmegaY.Expansion.Dynamics.earlier_branch
#print axioms OmegaY.Expansion.Dynamics.seed_step
#print axioms OmegaY.Expansion.Dynamics.seed_path
