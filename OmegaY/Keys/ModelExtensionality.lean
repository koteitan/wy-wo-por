/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Keys/ModelExtensionality.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
-/
import OmegaY.Model

/-!
# Model-label equality determines a finite key's named columns

Natural numbers embed injectively into the actual bounded-ordinal label
type. Consequently equality under every model-label interpretation implies
literal equality of the finite column names and infinity markers. The two
templates may have different source widths. Their equality then holds
under every interpretation into any linearly ordered label type.
-/

namespace OmegaY.Keys

open scoped Ordinal

noncomputable def naturalModelLabel (n : Nat) : Model.Label :=
  ⟨(n : Ordinal), ((Ordinal.natCast_lt_omega0 n).trans Ordinal.omega0_lt_omega_one).le⟩

theorem naturalModelLabel_injective : Function.Injective naturalModelLabel := by
  intro a b h
  have hOrdinal : (a : Ordinal) = (b : Ordinal) := congrArg Subtype.val h
  exact_mod_cast hOrdinal

/-- The test interpretation is a genuine member of the model's label
space; there is no extra abstract label-separation assumption. -/
theorem named_coordinates_eq_of_model_eval_eq {m n n' : Nat}
    (left : Template m n) (right : Template m n')
    (h : ∀ labels : Nat → Model.Label,
      eval left (fun c => labels c.val) = eval right (fun c => labels c.val))
    (i : Fin m) : (left i).map Fin.val = (right i).map Fin.val := by
  have he := congrFun (h naturalModelLabel) i
  simp only [eval, Pi.toLex_apply] at he
  cases hl : left i with
  | none =>
    cases hr : right i with
    | none => rfl
    | some b => simp only [hl, hr, WithTop.top_ne_coe] at he
  | some a =>
    cases hr : right i with
    | none => simp only [hl, hr, WithTop.coe_ne_top] at he
    | some b =>
      have hLabels : naturalModelLabel a.val = naturalModelLabel b.val := by
        simpa only [hl, hr, WithTop.coe_inj] using he
      exact congrArg some (naturalModelLabel_injective hLabels)

theorem eval_eq_of_named_coordinates_eq {m n n' : Nat}
    (left : Template m n) (right : Template m n')
    (h : ∀ i, (left i).map Fin.val = (right i).map Fin.val)
    {Label : Type*} [LinearOrder Label] (labels : Nat → Label) :
    eval left (fun c => labels c.val) = eval right (fun c => labels c.val) := by
  funext i
  have hi := h i
  simp only [eval, Pi.toLex_apply]
  cases hl : left i with
  | none =>
    cases hr : right i with
    | none => rfl
    | some b => simp only [hl, hr, Option.map_none, Option.map_some, reduceCtorEq] at hi
  | some a =>
    cases hr : right i with
    | none => simp only [hl, hr, Option.map_none, Option.map_some, reduceCtorEq] at hi
    | some b =>
      have hValue : a.val = b.val := by simpa only [hl, hr, Option.map_some, Option.some.injEq] using hi
      exact congrArg (fun x : Nat => (labels x : WithTop Label)) hValue

/-- Model-specific key equalities can be reused with natural column
labels, other ordinal labels, or any other linear order. -/
theorem eval_eq_of_model_eval_eq {m n n' : Nat}
    (left : Template m n) (right : Template m n')
    (h : ∀ labels : Nat → Model.Label,
      eval left (fun c => labels c.val) = eval right (fun c => labels c.val))
    {Label : Type*} [LinearOrder Label] (labels : Nat → Label) :
    eval left (fun c => labels c.val) = eval right (fun c => labels c.val) :=
  eval_eq_of_named_coordinates_eq left right (named_coordinates_eq_of_model_eval_eq left right h) labels

theorem nat_eval_eq_of_model_eval_eq {m n n' : Nat}
    (left : Template m n) (right : Template m n')
    (h : ∀ labels : Nat → Model.Label,
      eval left (fun c => labels c.val) = eval right (fun c => labels c.val)) :
    eval left (fun c => c.val) = eval right (fun c => c.val) :=
  eval_eq_of_model_eval_eq left right h id

end OmegaY.Keys

#print axioms OmegaY.Keys.named_coordinates_eq_of_model_eval_eq
#print axioms OmegaY.Keys.eval_eq_of_model_eval_eq
#print axioms OmegaY.Keys.nat_eval_eq_of_model_eval_eq
