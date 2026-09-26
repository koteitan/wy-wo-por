/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/PrefixDynamics.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Expansion.Totality
import OmegaY.Expansion.FinalHighEventSampling
import OmegaY.Expansion.LoopPrefix
import OmegaY.Canonical.Values

/-!
# Prefix dynamics of the actual finite expansion

Zero copies remove exactly the last input value. Each additional actual
block appends complete columns, so successful outputs from one source are
nested prefixes. These are executable combinatorial facts; no output
normality, numerical recognition, or trajectory well-foundedness is used.
-/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem prefix_bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl

theorem bottomValues_of_build {values : List Nat} {mountain : Mountain}
    (hBuild : Canonical.build values = .ok mountain) : bottomValues mountain = values := by
  have h := congrArg (List.map (fun value : Option Nat => value.getD 0)) (build_bottom_values hBuild)
  have hf : (fun column : Column => (Canonical.bottomValue column).getD 0) =
      (fun column : Column => (column[1]?.getD phantom).value) := by
    funext column
    unfold Canonical.bottomValue
    cases column[1]? <;> rfl
  have h' : bottomValues mountain = values.map (fun value : Nat => value) := by
    simpa only [Canonical.bottomValues, List.map_map, Function.comp_def, hf,
      Option.getD_some, bottomValues] using h
  exact h'.trans (List.map_id values)

theorem bottomValues_pop (mountain : Mountain) :
    bottomValues mountain.pop = (bottomValues mountain).take (mountain.size - 1) := by
  simp only [bottomValues, Array.toList_pop, List.dropLast_eq_take, List.map_take, Array.length_toList]

theorem PreservesColumns.bottomValues_prefix {before after : Mountain}
    (h : PreservesColumns before after) : List.IsPrefix (bottomValues before) (bottomValues after) := by
  have hColumns : List.IsPrefix before.toList after.toList := by
    apply List.prefix_iff_getElem?.mpr
    intro i hi
    have hi' : i < before.size := by simpa only [Array.length_toList] using hi
    simpa only [Array.getElem?_toList, Array.getElem_toList] using
      (h i hi').trans (Array.getElem?_eq_getElem hi')
  exact hColumns.map _

theorem PreservesColumns.pop_both {before after : Mountain}
    (h : PreservesColumns before after) : PreservesColumns before.pop after.pop :=
  ((PreservesColumns.pop_prefix before).trans h).between_prefixes (PreservesColumns.pop_prefix after)
    (by simpa only [Array.size_pop] using Nat.sub_le_sub_right h.size_le 1)

theorem expand_delete_of_trivial {values : List Nat} (hLegal : Legal values) (copies : Nat)
    (hTrivial : values = [] ∨ values.getLast? = some 1 ∨ copies = 0) :
    expand values copies = .ok (values.take (values.length - 1)) := by
  obtain ⟨initial, hBuild, hValid, _⟩ := build_total hLegal
  have hDiagram : expandDiagram values copies = .ok initial.pop := by
    simp [expandDiagram, hBuild, Except.mapError, hTrivial]
  have hValues := valuesOf_eq_bottomValues hValid.pop
  rw [bottomValues_pop, bottomValues_of_build hBuild, build_size hBuild] at hValues
  simpa only [expand, hDiagram, prefix_bind_ok] using hValues

theorem expand_zero {values : List Nat} (hLegal : Legal values) :
    expand values 0 = .ok (values.take (values.length - 1)) :=
  expand_delete_of_trivial hLegal 0 (Or.inr (Or.inr rfl))

theorem Preparation.blocks_preserved {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {i j : Nat} (hOrder : i ≤ j)
    {before after : Mountain}
    (hBefore : (forIn (List.range i) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok before)
    (hAfter : (forIn (List.range j) p.reduced (fun block mountain => do
      let next ← copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)
      pure (.yield next)) : Result Mountain) = .ok after) :
    PreservesColumns before after := by
  induction j, hOrder using Nat.le_induction generalizing after with
  | base =>
    have he : before = after := Except.ok.inj (hBefore.symm.trans hAfter)
    exact he ▸ (fun _ _ => rfl)
  | succ j hj ih =>
    obtain ⟨middle, hMiddle, ready⟩ := p.blocks_total hLast j
    obtain ⟨result, _, hStep, _, _, state, _⟩ := ready.copyBlock_with_history hLast
    have hSizes : p.initial.size = p.reduced.size := by
      have hi := build_size p.initial_build
      have hr := build_size p.reduced_build
      simp only [List.length_append, List.length_singleton] at hi hr
      omega
    have hStep' : copyBlock middle p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (j + 1) = .ok result := by
      simpa only [hSizes] using hStep
    have hRun := forIn_yield_range_succ p.reduced
      (fun block mountain => copyBlock mountain p.marked p.boundaries p.root.column
        (p.initial.size - 1 - p.root.column) (block + 1)) hMiddle hStep'
    have he : result = after := Except.ok.inj (hRun.symm.trans hAfter)
    exact he ▸ (ih hMiddle).trans state.start_preserved

theorem Preparation.expand_prefix_positive {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {i j : Nat}
    (hPositive : 0 < i) (hOrder : i ≤ j) {left right : List Nat}
    (hLeft : expand (front ++ [last]) i = .ok left)
    (hRight : expand (front ++ [last]) j = .ok right) : List.IsPrefix left right := by
  obtain ⟨before, hBefore, hBeforeReady⟩ := p.blocks_total hLast i
  obtain ⟨after, hAfter, hAfterReady⟩ := p.blocks_total hLast j
  have hLeftValues : expand (front ++ [last]) i = .ok (bottomValues before.pop) := by
    simpa only [expand, p.expandDiagram_of_blocks hLast hPositive hBefore, prefix_bind_ok] using
      valuesOf_eq_bottomValues hBeforeReady.valid.pop
  have hRightValues : expand (front ++ [last]) j = .ok (bottomValues after.pop) := by
    simpa only [expand, p.expandDiagram_of_blocks hLast (hPositive.trans_le hOrder) hAfter, prefix_bind_ok] using
      valuesOf_eq_bottomValues hAfterReady.valid.pop
  have heLeft : bottomValues before.pop = left := Except.ok.inj (hLeftValues.symm.trans hLeft)
  have heRight : bottomValues after.pop = right := Except.ok.inj (hRightValues.symm.trans hRight)
  exact heLeft ▸ heRight ▸ ((p.blocks_preserved hLast hOrder hBefore hAfter).pop_both.bottomValues_prefix)

theorem Preparation.front_prefix_of_expand_positive {front : List Nat} {last : Nat}
    (p : Preparation front last) (hLast : 1 < last) {copies : Nat} (hCopies : 0 < copies)
    {result : List Nat} (hRun : expand (front ++ [last]) copies = .ok result) :
    List.IsPrefix front result := by
  obtain ⟨diagram, hDiagram, hValid⟩ := OmegaY.Expansion.expandDiagram_total (build_success_legal p.initial_build) copies
  have hValues : valuesOf diagram = .ok result := by simpa only [expand, hDiagram, prefix_bind_ok] using hRun
  have he : bottomValues diagram = result := Except.ok.inj
    ((valuesOf_eq_bottomValues hValid).symm.trans hValues)
  have hPrefix := (p.expandDiagram_reduced_preserved hLast hCopies hDiagram).bottomValues_prefix
  rw [bottomValues_of_build p.reduced_build, he] at hPrefix
  exact (List.prefix_append front [last - 1]).trans hPrefix

theorem expand_prefix {values left right : List Nat} (hLegal : Legal values)
    {i j : Nat} (hOrder : i ≤ j)
    (hLeft : expand values i = .ok left) (hRight : expand values j = .ok right) :
    List.IsPrefix left right := by
  by_cases hTrivial : values = [] ∨ values.getLast? = some 1
  · have hLeftDelete := expand_delete_of_trivial hLegal i
      (hTrivial.imp_right Or.inl)
    have hRightDelete := expand_delete_of_trivial hLegal j
      (hTrivial.imp_right Or.inl)
    have he : left = right := Except.ok.inj
      (hLeft.symm.trans (hLeftDelete.trans (hRightDelete.symm.trans hRight)))
    exact he ▸ List.prefix_refl left
  · rcases hLegal with rfl | ⟨rest, rfl, hPositive⟩
    · exact (hTrivial (Or.inl rfl)).elim
    · rcases List.eq_nil_or_concat' rest with rfl | ⟨middle, last, rfl⟩
      · exact (hTrivial (Or.inr rfl)).elim
      · have hLastPositive : 0 < last := hPositive last (by simp)
        have hLastNe : last ≠ 1 := by
          intro h
          apply hTrivial
          right
          change ((1 :: middle) ++ [last]).getLast? = some 1
          rw [List.getLast?_append]
          simp [h]
        have hLast : 1 < last := by omega
        obtain ⟨p⟩ := preparation_total middle last
          (fun value hv => hPositive value (by simp [hv])) hLast
        change expand ((1 :: middle) ++ [last]) i = .ok left at hLeft
        change expand ((1 :: middle) ++ [last]) j = .ok right at hRight
        by_cases hi : i = 0
        · subst i
          have hZero := expand_zero (build_success_legal p.initial_build)
          have hLeftEq : left = 1 :: middle := by
            have he := Except.ok.inj (hLeft.symm.trans hZero)
            simpa using he
          rw [hLeftEq]
          by_cases hj : j = 0
          · subst j
            have he : left = right := Except.ok.inj (hLeft.symm.trans hRight)
            rw [← he, hLeftEq]
          · exact p.front_prefix_of_expand_positive hLast (Nat.pos_of_ne_zero hj) hRight
        · exact p.expand_prefix_positive hLast (Nat.pos_of_ne_zero hi) hOrder hLeft hRight

/-- Executable totality and nested outputs, without supplied successful
runs. The take equation states exactly which existing output is retained. -/
theorem expand_nested_total {values : List Nat} (hLegal : Legal values)
    (i j : Nat) (hOrder : i ≤ j) :
    ∃ left right, expand values i = .ok left ∧ expand values j = .ok right ∧
      right.take left.length = left := by
  obtain ⟨left, hLeft, _⟩ := expand_total hLegal i
  obtain ⟨right, hRight, _⟩ := expand_total hLegal j
  exact ⟨left, right, hLeft, hRight, (List.prefix_iff_eq_take.mp
    (expand_prefix hLegal hOrder hLeft hRight)).symm⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.bottomValues_of_build
#print axioms OmegaY.Expansion.expand_zero
#print axioms OmegaY.Expansion.Preparation.blocks_preserved
#print axioms OmegaY.Expansion.Preparation.expand_prefix_positive
#print axioms OmegaY.Expansion.Preparation.front_prefix_of_expand_positive
#print axioms OmegaY.Expansion.expand_prefix
#print axioms OmegaY.Expansion.expand_nested_total
